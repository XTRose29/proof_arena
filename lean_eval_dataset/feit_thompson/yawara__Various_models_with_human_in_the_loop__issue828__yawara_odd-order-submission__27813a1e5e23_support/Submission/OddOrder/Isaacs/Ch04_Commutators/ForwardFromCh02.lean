import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Submission.OddOrder.GroupTheory.ElementaryAbelian
import Submission.OddOrder.Isaacs.Ch02_Subnormality.Main

open scoped commutatorElement Pointwise

/-!
# Ch.4 → Ch.2 forward dependencies

このファイルは **Isaacs FGT Ch.2 §2D Thm 2.20 (Lucchini)** を完全形式化する場所.
論理的には Ch.2 の定理だが, **K = ⊥ case の証明が Ch.4 §4A-§4B (lower central series
加法性) に依存**するため, owner chapter (Ch.4) ディレクトリに置く.

## このファイルの構造

1. **補助補題群** (旧 Main.lean §4B から移動): `iterCommutator` infrastructure +
   `le_centralizer_of_isMinimalNormal` (Z(F(G)) absorbs G-minimal normal) +
   minimal normal nilpotent ⇒ elem abelian の variants + Lucchini K=⊥ Step 1 集約
   (`exists_isMinimalNormal_le_fitting_le_centralizer_fitting`).
   循環 import 回避のため Main.lean ではなくここに置く
   (Main.lean は Ch.3 → ForwardFromCh02 を経由するため transitive アクセス可).

2. `lucchini_K_bot_aux` — Lucchini の K = ⊥ case (private theorem).

3. `lucchini_aux` — `|G|`-induction wrapper (private).
   * K = ⊥ branch: `lucchini_K_bot_aux` を呼ぶ.
   * K > ⊥ branch: Ch.2 の `lucchini_K_pos_reduction` (subgroup correspondence のみ)
     + IH on G/K.

4. `lucchini_index_normalCore_lt_index` — **Isaacs Thm 2.20 本体** (theorem).
   `lucchini_aux (Nat.card G) le_rfl ...` で呼ぶ.

## namespace 設計

書籍上は Ch.2 の定理だが, Lean 上は物理的に Ch.4 dir にいるため
`OddOrder.Isaacs.Ch04` namespace を使う. docstring に book 番号 (Thm 2.20) を明示.

## 関連ノート

- [`notes/meta/forward_dep_policy.md`](../../../notes/meta/forward_dep_policy.md):
  forward dep の所在規則.
- [`notes/isaacs/ch02_subnormality.md`](../../../notes/isaacs/ch02_subnormality.md):
  Ch.2 内 `lucchini_K_pos_reduction` (構造補題) との分担.
- [`notes/isaacs/ch04_commutators.md`](../../../notes/isaacs/ch04_commutators.md):
  §4A-§4B 補助補題の inventory.
-/

namespace OddOrder.Isaacs.Ch04

variable {G : Type*} [Group G]

/-! ## 補助補題群: iterCommutator + minimal normal nilpotent variants

旧 `OddOrder/Isaacs/Ch04_Commutators/Main.lean` §4B 後半 (L1699-2024) から移動.
Lucchini K=⊥ 証明で使用する補題群. 循環 import 回避のため Main.lean ではなく本ファイルに置く. -/

/-! ### iterated right commutator infrastructure

Lucchini K = ⊥ case の「Z(F(G)) absorbs G-minimal normal」補題等で使用する.
`E, F ≤ G` に対し `iter E F n = ⁅...⁅E, F⁆, F⁆..., F⁆` (`n` 回右から `F`). -/

/-- **Iterated right commutator**: `iterCommutator E F n = ⁅...⁅E, F⁆, F⁆..., F⁆`. -/
def iterCommutator (E F : Subgroup G) : ℕ → Subgroup G
  | 0 => E
  | n + 1 => ⁅iterCommutator E F n, F⁆

@[simp]
theorem iterCommutator_zero (E F : Subgroup G) :
    iterCommutator E F 0 = E := rfl

@[simp]
theorem iterCommutator_succ (E F : Subgroup G) (n : ℕ) :
    iterCommutator E F (n + 1) = ⁅iterCommutator E F n, F⁆ := rfl

/-- **iterCommutator は F の lcs 経由で押し込められる**: `E ≤ F` ⇒
`iterCommutator E F n ≤ ((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype`.

特に `F` が冪零 (Group.IsNilpotent ↥F) なら, 十分大きな `n` で `lcs ↥F n = ⊥`,
よって `iterCommutator E F n = ⊥`. これが Lucchini K = ⊥ case の核心 (Z(F(G))
absorbs G-minimal). -/
theorem iterCommutator_le_lowerCentralSeries_map
    {E F : Subgroup G} (hE : E ≤ F) (n : ℕ) :
    iterCommutator E F n ≤ ((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype := by
  induction n with
  | zero =>
    simp only [iterCommutator_zero, Subgroup.lowerCentralSeries_zero]
    rw [← MonoidHom.range_eq_map, F.range_subtype]
    exact hE
  | succ n ih =>
    rw [iterCommutator_succ]
    have hRange : (⊤ : Subgroup ↥F).map F.subtype = F := by
      rw [← MonoidHom.range_eq_map]; exact F.range_subtype
    have hMapLcs : ((⊤ : Subgroup ↥F).lowerCentralSeries (n + 1)).map F.subtype =
        ⁅(((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype), F⁆ := by
      change ⁅(⊤ : Subgroup ↥F).lowerCentralSeries n, (⊤ : Subgroup ↥F)⁆.map F.subtype = _
      rw [Subgroup.map_commutator, hRange]
    rw [hMapLcs]
    exact Subgroup.commutator_mono ih le_rfl

/-- **iterCommutator は ambient G の lcs に押し込められる**: 任意 `E, F ⊆ G` で
`iterCommutator E F n ≤ (⊤ : Subgroup G).lowerCentralSeries n`. `E ≤ F` 不要
(E, F は ⊤ ≤ G で挟まれる).

`E ≤ ⊤` と `F ≤ ⊤` 経由で `iterCommutator E F n ≤ iterCommutator ⊤ ⊤ n = lcs G n`. -/
theorem iterCommutator_le_lowerCentralSeries (E F : Subgroup G) (n : ℕ) :
    iterCommutator E F n ≤ (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero =>
    simp only [iterCommutator_zero, Subgroup.lowerCentralSeries_zero]
    exact le_top
  | succ n ih =>
    rw [iterCommutator_succ, Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mono ih le_top

/-- **ambient G 冪零 ⇒ iterCommutator は最終的に ⊥** (任意 E, F).
`E ≤ F` 制約のない一般版 (上の `iterCommutator_eq_bot_of_isNilpotent` は `E ≤ F` 必要). -/
theorem iterCommutator_eq_bot_of_isNilpotent_ambient
    [Group.IsNilpotent G] (E F : Subgroup G) :
    ∃ n, iterCommutator E F n = ⊥ := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹_›
  refine ⟨n, le_antisymm ?_ bot_le⟩
  exact (iterCommutator_le_lowerCentralSeries E F n).trans (le_of_eq hn)

/-- **冪零 ambient G + nontrivial normal E ⇒ ⁅E, F⁆ < E**: 厳密降下.

`⁅E, F⁆ = E` なら iterCommutator E F は定常 (induction で各 n で = E). しかし
`iterCommutator_eq_bot_of_isNilpotent_ambient` で ∃ n, iter = ⊥. ⇒ E = ⊥ 矛盾. -/
theorem commutator_lt_self_of_isNilpotent_ambient
    [Group.IsNilpotent G] {E F : Subgroup G} [E.Normal] (hE : E ≠ ⊥) :
    ⁅E, F⁆ < E := by
  refine lt_of_le_of_ne (Subgroup.commutator_le_left E F) ?_
  intro heq
  have hconst : ∀ n, iterCommutator E F n = E := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iterCommutator_succ, ih]
      exact heq
  obtain ⟨n, hn⟩ := iterCommutator_eq_bot_of_isNilpotent_ambient E F
  rw [hconst n] at hn
  exact hE hn

/-- **iterCommutator は normal を保つ**. `E, F ⊴ G` ⇒ `iter E F n ⊴ G`. -/
theorem iterCommutator_normal {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    (iterCommutator E F n).Normal := by
  induction n with
  | zero => exact ‹E.Normal›
  | succ n ih =>
    haveI := ih
    rw [iterCommutator_succ]
    infer_instance

/-- **iterCommutator は antitone (decreasing)**. `E, F ⊴ G` ⇒
`iter E F (n+1) ≤ iter E F n`.

(直観: `iter E F n ⊴ G ⊇ F` で `F` は `iter E F n` を normalize するので
`⁅iter, F⁆ ≤ iter`.) -/
theorem iterCommutator_succ_le_self {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    iterCommutator E F (n + 1) ≤ iterCommutator E F n := by
  haveI : (iterCommutator E F n).Normal := iterCommutator_normal n
  rw [iterCommutator_succ]
  exact Subgroup.commutator_le_left (iterCommutator E F n) F

/-- **F 冪零 ⇒ iterCommutator は最終的に ⊥**: `E ≤ F` + `F` (as group `↥F`) が冪零
⇒ ∃ n, `iter E F n = ⊥`. -/
theorem iterCommutator_eq_bot_of_isNilpotent
    {E F : Subgroup G} (hE : E ≤ F) [hF : Group.IsNilpotent ↥F] :
    ∃ n, iterCommutator E F n = ⊥ := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hF
  refine ⟨n, le_antisymm ?_ bot_le⟩
  calc iterCommutator E F n
      ≤ ((⊤ : Subgroup ↥F).lowerCentralSeries n).map F.subtype :=
        iterCommutator_le_lowerCentralSeries_map hE n
    _ ≤ ⊥ := by rw [hn]; exact (Subgroup.map_bot F.subtype).le

/-- **iterCommutator は E 内に留まる**: `E, F ⊴ G ⇒ iter E F n ≤ E`. -/
theorem iterCommutator_le_self {E F : Subgroup G} [E.Normal] [F.Normal] (n : ℕ) :
    iterCommutator E F n ≤ E := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact (iterCommutator_succ_le_self n).trans ih

/-- **Z(F(G)) absorbs G-minimal normal in F(G)** ⭐ (Lucchini K=⊥ aux 解消の核補題):
`E ⊴ G` minimal normal, `E ≤ F`, `F ⊴ G` 冪零 ⇒ `E ≤ centralizer F`.

**証明** (Isaacs §4A lcs 経路):
1. `iterCommutator E F` の降下列を考える. 各項は G-normal (`iterCommutator_normal`),
   decreasing (`iterCommutator_succ_le_self`), `E` 内 (`iterCommutator_le_self`).
2. `F` 冪零 で `iter n = ⊥` for some `n` (`iterCommutator_eq_bot_of_isNilpotent`).
3. 最小 `k` で `iter k = ⊥` を取る. `k = 0` だと `E = ⊥` で `E` minimal 仮定と矛盾.
4. `k = j + 1` で, `iter j ≠ ⊥`, `iter j ⊴ G`, `iter j ≤ E`. **E の minimality**
   より `iter j = E`.
5. `⁅E, F⁆ = ⁅iter j, F⁆ = iter (j+1) = iter k = ⊥`. 故に `E ≤ centralizer F`.

**下流**: Ch.2 §2D Lucchini K=⊥ aux. -/
theorem le_centralizer_of_isMinimalNormal {E F : Subgroup G}
    (hMin : OddOrder.Isaacs.Ch02.IsMinimalNormal E) (hEF : E ≤ F)
    [F.Normal] [Group.IsNilpotent ↥F] :
    E ≤ Subgroup.centralizer (F : Set G) := by
  classical
  haveI hE_norm : E.Normal := hMin.1
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  -- Find smallest k with iter E F k = ⊥.
  have hExists : ∃ k, iterCommutator E F k = ⊥ :=
    iterCommutator_eq_bot_of_isNilpotent hEF
  set k := Nat.find hExists with hk_def
  have hk_iter : iterCommutator E F k = ⊥ := Nat.find_spec hExists
  -- k = 0 ⇒ E = ⊥, 矛盾.
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · exfalso
    rw [hk0, iterCommutator_zero] at hk_iter
    exact hMin.2.1 hk_iter
  -- k = j + 1, j minimality に達しない.
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
  have hIter_j_ne : iterCommutator E F j ≠ ⊥ := fun h => by
    have hjk : j < k := hj ▸ Nat.lt_succ_self j
    exact absurd (Nat.find_min' hExists h) (not_le.mpr hjk)
  haveI : (iterCommutator E F j).Normal := iterCommutator_normal j
  have hIter_j_le : iterCommutator E F j ≤ E := iterCommutator_le_self j
  rcases hMin.2.2 _ inferInstance hIter_j_le with h_bot | h_eq_E
  · exact absurd h_bot hIter_j_ne
  · -- iter j = E, hence ⁅E, F⁆ = iter (j+1) = iter k = ⊥.
    rw [← h_eq_E, ← iterCommutator_succ,
        show j + 1 = k from hj.symm]
    exact hk_iter

                                                                                 

                                                                                                       
                                                                                                          
                                                 
                         
                                                                 
                        
                                                      
                                                                               
                                          
                                                       

                                                                          
                                                         

                                                                                             
                                                                                                      
                                                               
                                    
                                                                    
                              
                                                 
                                     
                                                                                  
                                                                               
                                                                      
                                            
                                                                 
              
                                 
                 
                                                                                       
                                                 
                                                         

                                                                                          
                                                     

                                                                            
                                                                                                               
                                                                    

                                                                                                                 
                                                                        
                                                                     
                                    
                                                                    
                              
                                                          
                                     
                                        
                                                                            
                                         
                                                          
                                                                                  
                                                            
                                                                              
                              
                                               
                                               
                          
                                
                           
                    
                       
                              
                              
                              
                                                                                     
                                                                   
                                           
                    
                  
                             
                              
                                   
                                        
                                             
                 
                           
                         
                          
                                 
                                                                               
                               
                                               
                                
             
                                   
                                     
                                  
              
                                 
                                       
                        
                                                              
                                             
                            
             
                                                                             
            
                                  
                                                                        
                                      
                                                           
                             
                                                                         
                                                  
                            
                                        
                                         
                      

                                                                                             
                                                     
              
                                            
                                                       

                                                                                           
                                   
                                                                                       
                                                                      
                            
                                                                                   
                                                                              
                                

                                                                                   
                                                                
                                                   
                    
                                                     
                                      
                                               
                                                
                                              
                                                                                            
                                   
                               
                                                          
            
                                                                                          
           
                       
                               
                                                                   
                                                         
                                                                         
                                            
                                          
                                                                   
                            
                                    
                                                                      
                                                    
                                                   

/-! ## Lucchini K = ⊥ aux + 本体 -/

                                                                                                      
                                                             
                                                              
                                                                            
                                                                      
                              
         

/-- Every subgroup of a cyclic group is characteristic.

This proof uses a generator directly: an automorphism sends the generator to another power of the
generator, so it sends each element `x` of a subgroup to an integral power of `x`, still in that
subgroup. -/
theorem characteristic_of_subgroup_of_isCyclic
    {C : Type*} [Group C] [IsCyclic C] (H : Subgroup C) :
    H.Characteristic := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  rw [Subgroup.mem_comap]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (φ g))
  have hφx : φ x = x ^ m := by
    calc
      φ x = φ (g ^ n) := by rw [hn]
      _ = (φ g) ^ n := by rw [map_zpow]
      _ = (g ^ m) ^ n := by rw [hm]
      _ = g ^ (m * n) := by rw [← zpow_mul]
      _ = g ^ (n * m) := by rw [mul_comm]
      _ = (g ^ n) ^ m := by rw [zpow_mul]
      _ = x ^ m := by rw [hn]
  change φ x ∈ H
  rw [hφx]
  exact H.zpow_mem hx m

                                                                                      
                                                              
                                          
                                                                             
                          
                                         
                                       
                                                                                
                                           
               
                         
                                            
                                                                                 
                       
                                                            
                                                         
                                                         
                                                                     
                                                                 
                                 

                                                                         

                                                                                    
                                                             

                                                        
                                                                                            
                                              
                                                                
                                                                                                      
                                                                                   
                                                   
                                                                                                             
                                                                                                      
                                           
                                                          
                          
                 
                                                   
                                             
                                                       
         
                  
           
                             
                                                      
                
                                         
                                      
                                        
                         
                                    
                                                    
                                                      
                             
                                              
                                                  
                                                               
                                                                
                                             
                
                                                    
                      
                        
                                            
                                      
                                             
                      
                                                    
                     
                                  
               
                                                               
                                                   
                                   
                             
                                                                                        
                                                                                 
                                                                            
                                          
                                             
                                                                                              
                                         
                                                    
                                         
                                                                      
                                                                                    
                        
                                                                                                  
                                                                                                  
                                       
                              
                    
                                                                                       
                                                                                                                    
                                     
                                                                                 
                                                             
                                                                                                                
                                                                                           
                                                                                           
                                                                
                                                                            
                                       
                                                                                            
                                                                    
                                 
                                                                           
                                                                                        
                                   
                                                   
                                                  
                     
                                     
                                     
                                                             
                               
                                                                     
                                            
                                             
                                                                                            
                                                     
                                   
                                                                      
                                                                                         
                     
                                                   
                          
                   
                        
                  
                             
                                                                                      
                                                                                                 
                                            
                                                         
                                                             
                     
                     
                                                    
                                                                            
                                                                        
                                                                       
                                                    
                                             
                                  
                                   
                                                   
                                                                            
                                                        
                                                         
                  
                                      
                              
                  
                                                                                       
                                                     
                                                   
                               
                          
                   
                                                                     
                                   
                            
                                       
                    
                                                                   
                       
                                      
                                      
                                                                         
                     
                                                                 
                                                      
                                                                     
                                                            
                                                             
                                                          
                                               
             
                   
                                                                       
                                               
                                                  
                                              
                                                             
                                                                     
                                                    
                 
                                  
                   
                                       
                            
                                
                   
                 
                       
                                        
                                         
                                                                                              
                                                                 
                
                                                       
                                              
                         
                                            
                                                                
                     
                                               
                 
                                           
                                            
                                                
                                   
               
                      
                                                                     
                                         
                                       
                                                                                      
                                       
                   
                              
                                                       
                                                       
                                                                             
                                                                                
                                                            
                                                            
                      
                                                                                  
               
                                              
               
                                              
                           
                          
                                                                                  
                                                      
                  
                             
                                         
                    
                                                         
                                                                
                                                                          
                               
                                                            
                                          
                                                                          
                                    
                        
                                               
                                                                                                   
                                                 
                                                          
                    
                                                                    
                                                                          
                                                                                           
                                                                                   
                                                                                         
                                                                         
                                                     
                               
                     
                                                                                        
                                                                                           
                                                                
                                                              
                                                                               
                                                                         
                                                                                          
                                                                       
                                                           
                                        
                                                    
                           
                                      
                                                                  
                     
                                          
                                 
                                                                                       
                                                        
                                                        
                    
                                                      
                                                                          
                                                               
                             
                                                  
                                                          
                                               
                                                        
                                                                                                  
                        
                                                                                              
                                                                                              
                          
                                                              
                                                   
                    
                                                                 
                                                                             
                         
                                                  
                                           
                                                                      
                                                                      
                                                                       
                                                 
                         
                    
                                                    
                                                                      
                                                                      
                                                                       
                                                 
                         
                    
                                                                       
                                                                                                       
                                                                              
                                                                        
                                                         
                         
               
                                                                                                       
                                                                              
                                                                        
                                                         
                         
               
                                                            
                                                    
                                   
                                                           
                                                                
                                                   
                                                               
                                                
                                                             
                                                     
                                                                             
                                                                     
                                           
                                         
                                                                 
                                                           
                                                                 
                                                                      
                                                             
                             
                                                                                      
                                                  
                                                                
                                                                        
                                      
                                                        
                                                                                           
                                                       
                                                       
                                                                 
                                                                    
                                                                                        
                                                            
                                                                                       
                                          
                                             
                                                   
                                        
                                              
                                                 
                                                                                                 
                                                              
                             
                                           
                                      
                                              
                       
                        
                                                                       
                                                      
                                    
                                     
                           
                                                  
                             
                             
                                                                                     
                                             
                                                                           
                                                     
                      
                                     
                      
                                             
                                                                       
                                                       
                                                                           
                                        
                                                  
                                                        
                                   
                                                                              
                                             
                                                               
                                                  
                 
                                                        
                                      
                              
               
                                              
                           
                                  
                                                   
                                                     
                                                                       
                                        
                                                  
                                                                                
                                                                            
                                                        
                        
                                                                       
                                                                                  
                                           
                 
                            
                                   
                                                            
                                                                        
                                                                                    
                 
                                                
                 
                                                
                             
                            
                                                                                    
                                                        
                    
                               
                                           
                      
                                    
                                                                   
                                                                                  
                                                                                              
                         
                                                                                 
                                                                         
                                                              
                                                                               
                                  
                      
                       
                     
                                                   
                                                                    
                                                       
                                          
                                               
                               
                   
                                                 
                                                            
                                                                         
                                                           
                                                          
                                                                           
                                                                                
                              
                                                                                 
                                                                             
                       
                                                    
                                                
                                                           
                                                 
                                        
                                                       
                                                     
                                               
                                                                    
                                
                      
                                          
                                                                             
                                                
                                                        
                    
                                          
                        
                                      
                            
                        
                         
                                                           
                        
                                                                                    
                                              
                                                  
                            
                                               
                                                                   
                                                  
                                           
                             
                    
                                      
                                                     
                                       
                            
                                                                                
                                                                                 
                                                    
                                                        
                                                                          
                                        
                      
                                                                           
                                             
                                                          
                                                                               
                                                                                                
                         
                           
                                                      
                                                                      
                                                             
                                                                                           
                                                           
                                                              
                                                                          
                               
                                     
                                                                          
                                                                      
                                          
                    
                                      
                 
                                                                     
                                                                        
                                                                     
                                
                                                
                             
                            
                                                                                    
                                                          
                                                     
                                                                          
                               
                                                        
                                               
                                                       
                                                     
                           
                                                      
                      
              
                                                             
                                                      
                                             
                                                      
                                             
                                           
                                                                     
                                                                       
                                                      
                                   
                                                         
                                                  
                                                        
                                   
                                                                              
                                             
                                                               
                              
                                                                
                                                   
                                                                            
                                                         
                                            
                                      
                              
                  
                                                                                       
                                                     
                                                   
                                                        
                         
                                
                   
                                                                     
                                   
                            
                                       
                    
                                                                   
                       
                                      
                                      
                                                                         
                     
                                                    
                                                                                
                                
                                                      
                                                                     
                                                            
                                                             
                                                             
                                               
             
                                 
                                                                  
                                               
                                            
                                                                           

                                                          

                                                                                              

                                                            
                                                              
                         
                                                     
                                                     
                                   
                                 
                                                                        
                                                                

                                                                                            
                                                                 

                                              
                                                                      
                                    

                                                                                                            
                                                                  
                                                                                   
                                                                      
                         
                                                     
                                                       
                                                  
                                                              

end OddOrder.Isaacs.Ch04
