import Submission.OddOrder.Isaacs.Ch04_Commutators.Main.CommutatorBasics

/-!
# ThreeSubgroups

Prefix-split from `OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroupsCoprime` (2000-line limit, issue 0103 第 2 パス).
-/

/-!
# Isaacs §4B-§4D 前半 — three subgroups, Mann, coprime action, [G,A] (pp. 122-141)

Split from the former monolithic `OddOrder.Isaacs.Ch04_Commutators.Main` (directory split, issue 0103).
-/
namespace OddOrder.Isaacs.Ch04
open scoped commutatorElement

variable {G : Type*} [Group G]


section /- 4B: Three-subgroups + lcs additivity + Mann (pp. 122-131) -/

/-! ### Isaacs §4B (Three-subgroups + lower central series)

- **Lemma 4.9 Three-subgroups**: mathlib `Subgroup.commutator_commutator_eq_bot_of_rotate`
  で完全カバー (前提 `⁅⁅H₂,H₃⁆, H₁⁆ = ⊥ ∧ ⁅⁅H₃,H₁⁆, H₂⁆ = ⊥ ⇒ ⁅⁅H₁,H₂⁆, H₃⁆ = ⊥`).
  no-wrapper. -/

/-- **Isaacs Cor 4.10** (Three-subgroups mod `N`):
`N ⊴ G` を含む形での 4.9 — `⁅⁅H₂, H₃⁆, H₁⁆ ≤ N ∧ ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N
⇒ ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N`.

商写像 `G → G/N` で push し, image 上で mathlib `commutator_commutator_eq_bot_of_rotate`
を適用. -/
theorem commutator_commutator_le_of_rotate {H₁ H₂ H₃ N : Subgroup G} [N.Normal]
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) :
    ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  -- Use `≤ N ↔ map (mk' N) = ⊥` (since ker (mk' N) = N).
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have to_quot : ∀ {K : Subgroup G}, K ≤ N ↔ K.map π = ⊥ := by
    intro K
    rw [eq_bot_iff, Subgroup.map_le_iff_le_comap]
    constructor
    · intro h x hx
      rw [Subgroup.mem_comap, hπ, Subgroup.mem_bot, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
      exact h hx
    · intro h x hx
      have := h hx
      rw [Subgroup.mem_comap, hπ, Subgroup.mem_bot, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at this
      exact this
  rw [to_quot]
  rw [to_quot] at h1 h2
  -- Map distributes over commutator.
  simp only [Subgroup.map_commutator] at h1 h2 ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

                                                                                           

                                                                                                    
                                                                                                    
                     

                                                                          
                                                                                        
                                                                                       
                                                                                                  
                                                                                                 
                                                            
                                                                                  
                                             
                                                                                                     
                                                                             

                                                                               
                                                  
                                                      
                                                                                              
                                                             
                                 
           
                                                                                     
                                                                                
                                                   
                   
                
                                                                              
                                                   
                                                                                    
                                                      
                                                               
                                                     
                                                                  
                                                                                                       
                                                               
                                            
                  
                              
                                                          
                        
                                                                  
                                                                              
                                                    
                                                                                               
                                                       
             
                                                        
                                                                         
                                 
             

/-- **左結合 n-重交換子**: `iterLeftCommutator g [g₁, g₂, ..., gₙ] = ⁅...⁅⁅g, g₁⁆, g₂⁆..., gₙ⁆`.
`gs.length = n` のとき重み `n+1`. -/
def iterLeftCommutator (head : G) (tail : List G) : G :=
  tail.foldl (fun acc g => ⁅acc, g⁆) head

                                                                                            
                                                       
                                                                         
                                                                            
                                                                                             
                                      
          
                                         
                     
                                                                                 
                                                                                    
                                                                                               
                                                                        
                                             
                                                                                
                                                                    
                                    
             
                                                                                                     
                                                     
              

                                                                                            
                                                                                     

                                                                                     
                                            
                                                                         
                                                                                     
                                                               
                                           

                                                                 
                                                       

                                                                                             
                                                                                                     
                                       

                                         
                                                                      
                                                                      
                                                                 
                                                                                         
                                                                                    

                                                                                         
                                                                                               
                                                                       
                                                                                 
                  
                
                
                           
                                                   
                                                                 
                                                                   
                                        
                                                                                    
                                              
                                                                       
                 
                                                     
                       
               

                                                                   
                                                                             

                                                                                                                 
                                                                                                    
                                      

                                                                                        
                                                                                                   
                                            
                                                         
                                                                   
                                                 
                                           
                                                          
                                                         
                 
                                        
                                                                              
                                                             
                                                    
                                                           
                

/-! ### iterCommutator + Z(F(G)) absorbs G-minimal 補題群

`iterCommutator E F n = ⁅...⁅E, F⁆, F⁆..., F⁆` の infrastructure と
`le_centralizer_of_isMinimalNormal` (Z(F(G)) absorbs G-minimal in F(G)) 系は
**`OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh02.lean`** に移動 (2026-05-24).

理由: Lucchini K=⊥ aux 解消 (issue #0001) で同じ補助補題群を使うが,
ForwardFromCh02 → Main.lean の direct import は循環依存になる
(Main → Ch3 → ForwardFromCh02 → Main). ForwardFromCh02 に置くことで Main.lean
からは Ch3 経由で transitive にアクセス可能 (namespace `OddOrder.Isaacs.Ch04` を共有).

Main.lean 側で `iterCommutator` を使う §4C `iterCommutator_add` / §4D
`iterCommutator_inl_inr_two_eq_one` は ForwardFromCh02 の declarations を直接参照. -/

/-! **Mann 4.14-4.19**: M(G), self-centralizing normal abelian 系. Isaacs 独自集約で
**BG/Peterfalvi 直接被引用 0**. ⇒ **Phase 1 内では skip 可** (audit 確認). -/

end -- 4B

section /- 4C: A acts on G via automorphisms (pp. 131-138) -/

/-! ### Isaacs §4C (A 作用 + [G,A])

`A ⊆ Aut(G)` の作用下で `[G, A]` (= smallest A-invariant N with A trivial on G/N) の構造論.

- **Lemma 4.20**: `⁅G, A⁆` は `A` が trivial 作用する最小 A-invariant 正規部分群.
- **Cor 4.21**: TFAE: (a) 右剰余類すべて A-inv, (b) 左剰余類すべて A-inv, (c) `⁅G,A⁆ ⊆ H`.
- **Thm 4.22**: A faithful + `⁅G, A, ..., A⁆_m = 1` ⇒ A solvable, derived length ≤ m-1.
- **Cor 4.23**: m=2 版.
- **Thm 4.24**: A faithful + chain ⇒ A nilpotent.
- **Lemma 4.25**: `⁅G,A,A⁆ = 1` ⇒ `⁅G,A⁆` abelian.
- **Thm 4.26**: A p-群 + chain ⇒ `⁅G,A⁆` は p-群.
- **Thm 4.27**: A 有限 + chain ⇒ `⁅G,A⁆` nilpotent.

全 stub. `[G, A]` の Lean 形式化 (semidirect product `G ⋊ A` 経由 vs `MulAut` 経由)
の設計判断が要る. ~500-800 行 LOC 推定. -/

end -- 4C

section /- 4D: Coprime action — Fitting + Thompson PxQ + Baer (pp. 138-146) -/

/-! ### Isaacs §4D (Coprime action) ⭐ FT クリティカル

BG Prop 1.6(a)(b)(c)(d)(e) クラスタ + BG Thm 1.11 がこの section を占める.

- **Lemma 4.28** ⭐ BG Prop 1.6(a): `(|G|,|A|) = 1` + (A or G solvable)
  ⇒ `G = C_G(A) · ⁅G, A⁆`.
- **Lemma 4.29** ⭐ BG Prop 1.6(b): coprime ⇒ `⁅G, A, A⁆ = ⁅G, A⁆`.
- **Cor 4.30**: A faithful + chain ⇒ `|A|` の素因子 ⊆ `|G|` の素因子.
- **Thm 4.31 Thompson P×Q** ⭐: `A = P × Q` (P p-群, Q p'-群) acts on p-群 G,
  Q fixes every P-fixed element ⇒ Q trivial on G.
- **Lemma 4.32**: P p-群, G 非自明 p-群: `⁅G, P⁆ < G` かつ `C_G(P) > 1`.
- **Thm 4.33**: G p-solvable ⇒ 全 p-local H で `O_{p'}(H) ≤ O_{p'}(G)`. **Hall-Higman 1.2.3
  (Ch.3 Lem 3.21) 経由**.
- **Thm 4.34 Fitting** ⭐ BG Prop 1.6(d): G abelian + coprime ⇒ `G = C_G(A) × ⁅G, A⁆`.
- **Cor 4.35** ⭐ BG Prop 1.6(e): G abelian p-群 + A p'-群 fixes order-p elements
  ⇒ A trivial.
- **Thm 4.36** ⭐ BG Thm 1.11: p > 2, G p-群 + A p'-群 fixes order-p elements
  ⇒ A trivial. **Ch.5 Cor 5.30 経由で normal p-comp 5.26 へ**.
- **Lemma 4.37 Baer trick**: G odd order + class ≤ 2 ⇒ `x +' y := xy√⁅y,x⁆` で加法群.
- **Thm 4.38**: p > 2, P p-群 + Q ⊴ A p'-群, Q fixes P-fixed elements ⇒ Q trivial
  (4.31 強化, P 正規不要).

**実装スケジュール推定**: 4.28 + 4.29 + 4.30 (~200 行 / 1 週), 4.34 + 4.35 + 4.36
(~250 行 / 1-2 週), 4.31 + 4.32 + 4.38 (~150 行 / 1 週), 4.33 + 4.37 (~150 行 / 1 週).

合計 ~750 行 LOC / 4-5 週. Phase 1 残予算と要相談. -/

/-- A finite `p`-group is a `{p}`-group in the π-group sense. -/
theorem isPiGroup_singleton_of_isPGroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} (hH : IsPGroup p H) :
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H := by
  intro q hq
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := H)).mp hH
  rw [hn] at hq
  by_cases hn0 : n = 0
  · simp [hn0] at hq
  · rw [Nat.primeFactors_prime_pow hn0 Fact.out] at hq
    simpa using hq

/-- A finite `{p}`-group in the π-group sense is a `p`-group. -/
theorem isPGroup_of_isPiGroup_singleton {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) H) :
    IsPGroup p H := by
  rw [IsPGroup.iff_card]
  exact ⟨(Nat.card H).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun {q} hq_prime hq_dvd => by
      have hq_pf : q ∈ (Nat.card H).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd, Nat.card_pos.ne'⟩
      simpa using hH q hq_pf)⟩

/-- Singleton π-core agrees with the usual `p`-core. -/
theorem oPiCore_singleton_eq_opCore {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] :
    OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G =
      OddOrder.Isaacs.Ch01.opCore p G := by
  apply le_antisymm
  · exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore
      (isPGroup_of_isPiGroup_singleton (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup ({p} : Set ℕ)))
  · exact OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore
      (isPiGroup_singleton_of_isPGroup (OddOrder.Isaacs.Ch01.opCore_isPGroup p G))

                                 
                                                           
                                           
                                                  
                                               
                                                 
                                                                          
                                                                 

                                                                                               
                                                             
                                                             
                        
                                                   
                                                                                                
                   
                                             
         
                                                           
                                  
                                                             
                              
                                                                                            
                       
                                                                                        
                                                                          
                                                                      
                                                            
                                            
                   
                           
                                            

                                                                    
                              
                                                                                     
                                                                   
                                                           
                                                                        
                                                    
                                                                                         
                                                
                                                   
                                                                                         
                                                                           
                              
              
                            
                                                    
                
                                        
                            
                                    
               
                                                               
                                     
                                                                               
                                                   
                                             
                                                              
                                                
             
                   
                   
                                    
                                                                    
                   
                   
                                        
                                                               
                    
                                                      
                                             
                                                                           
                                    
                              
                                      
                                                               
                                                                   
                                                           
                                                        
                                                 
                                                                    
                                         
                                                             
                                                          
                                  
                              
                                                                           
               
              
                                                     
                          
                     
            
                                 
                                
                                                
            

                                     
                                                                          
                                    
                                              
                                                     
                                                                               
                                                         
                                           
                                      

                                                                 
                                                          
                                                                                            
           
                                                                                                     
                                                                                     
                                                       
                                                             
              
                                                                           
                                                                   
                   
                                                                       
                                                             
                                                                   
                                               
                                             
                                                                                                        
           
                                                                           
                                   
                                                         
                                          
                                                    
                                                                    
                                                                                           
                                                                                                      
                                                                                             
                                             
                                                                      
           
                                                                    
                                           

                                                                       
                          
                                                             
                                                          
                                                                               
                                                                      
                                           
                                                 
                                                                   

                                                                                 
                                                      
                                                             
                                            
                       
                                                                                  
                                                          
                                                                          
                                      
                                                      
                                                                    
                                               
                                                                       
                 
                                                                                             

                                                                              
                                                                                   
                                                                    
            
                                  
         
                                                                               
                                                                  
                         
                                                          
                                              
                                           
                                                  
                                                   
                       
                                                                            
                                     
                                                            
                         
                                                            
                          

/-- **作用交換子部分群** `[G, A]_φ` := 集合 `{g * (φ a) g⁻¹ : g ∈ G, a ∈ A}` の生成部分群.

これは Γ = G ⋊[φ] A 内で `⁅inl(G), inr(A)⁆` を `inl : G →* Γ` 経由で pull back した
ものに対応する. 具体的計算: `[inl(g), inr(a)] = inl(g * (φ a) g⁻¹)` (`inl_aut` 経由).

下流 Isaacs §4D 4.28-4.30 の `[G, A]` 記号の自然な実装. -/
def actionCommutator {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ g : G, ∃ a : A, x = g * (φ a) g⁻¹}

/-- 自明作用 (φ = 1) の場合, `actionCommutator = ⊥` (各 generator = g * g⁻¹ = 1). -/
@[simp]
theorem actionCommutator_one_eq_bot {A G : Type*} [Group A] [Group G] :
    actionCommutator (1 : A →* MulAut G) = ⊥ := by
  rw [actionCommutator, Subgroup.closure_eq_bot_iff]
  rintro _ ⟨g, a, rfl⟩
  show g * (1 : MulAut G) g⁻¹ = 1
  simp

/-- **`actionCommutator φ` は φ 作用下で A-不変**.

`(φ b) (g * (φ a) g⁻¹) = (φ b) g * (φ (b * a * b⁻¹)) ((φ b) g)⁻¹` (generator → generator 写像)
が両方向で成り立つので生成集合自体が `(φ b)`-stable. `closure_of_invariant_set` で結論. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (actionCommutator φ) := by
  apply OddOrder.Isaacs.Ch03.IsAInvariant.closure_of_invariant_set
  intro b
  -- generator g * (φ a) g⁻¹ → (φ b) g * (φ (b·a·b⁻¹)) ((φ b) g)⁻¹ (= 別の generator).
  have key : ∀ g : G, ∀ a : A,
      (φ b) (g * (φ a) g⁻¹) = (φ b) g * (φ (b * a * b⁻¹)) ((φ b) g)⁻¹ := by
    intro g a
    rw [map_mul (φ b)]
    congr 1
    -- (φ b) ((φ a) g⁻¹) = (φ (b·a·b⁻¹)) ((φ b) g)⁻¹
    rw [show ((φ b) g)⁻¹ = (φ b) g⁻¹ from (map_inv (φ b) g).symm,
        show φ (b * a * b⁻¹) = (φ b) * (φ a) * (φ b)⁻¹ from by rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  ext x
  refine ⟨?_, ?_⟩
  · -- (φ b) '' S ⊆ S
    rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    exact ⟨(φ b) g, b * a * b⁻¹, key g a⟩
  · -- S ⊆ (φ b) '' S: take preimage via (φ b)⁻¹
    rintro ⟨g, a, rfl⟩
    refine ⟨(φ b)⁻¹ g * (φ (b⁻¹ * a * b)) ((φ b)⁻¹ g)⁻¹,
      ⟨(φ b)⁻¹ g, b⁻¹ * a * b, rfl⟩, ?_⟩
    rw [map_mul (φ b)]
    congr 1
    · exact MulAut.apply_inv_self (M := G) (φ b) g
    -- (φ b) ((φ (b⁻¹·a·b)) ((φ b)⁻¹ g)⁻¹) = (φ a) g⁻¹
    rw [show ((φ b)⁻¹ g)⁻¹ = (φ b)⁻¹ g⁻¹ from (map_inv ((φ b)⁻¹) g).symm,
        show φ (b⁻¹ * a * b) = (φ b)⁻¹ * (φ a) * (φ b) from by rw [map_mul, map_mul, map_inv],
        MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.apply_inv_self]

/-- **`(actionCommutator φ).map inl = ⁅inl.range, inr.range⁆`** (Γ = G ⋊[φ] A 内).

Γ 経由で `actionCommutator` を Γ 内 commutator subgroup と同一視. `inl` 経由 push が
Γ 内 commutator `⁅inl.range, inr.range⁆` に一致. これと Lem 4.1 (`⁅H, K⁆ ⊴ ⟨H, K⟩`)
を組合せて `(actionCommutator φ).Normal` (G 内) を導出する経路の主補題.

**証明**: 両側 `Subgroup.closure` 形に展開し集合等式. 生成元の対応は
`⁅inl g, inr a⁆ = inl (g * (φ a) g⁻¹)` (`SemidirectProduct.commutator_inl_inr`). -/
theorem actionCommutator_map_inl
    {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    (actionCommutator φ).map (SemidirectProduct.inl : G →* G ⋊[φ] A) =
      ⁅(SemidirectProduct.inl : G →* G ⋊[φ] A).range,
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range⁆ := by
  rw [actionCommutator, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    refine ⟨SemidirectProduct.inl g, ⟨g, rfl⟩, SemidirectProduct.inr a, ⟨a, rfl⟩, ?_⟩
    exact SemidirectProduct.commutator_inl_inr (φ := φ) g a
  · rintro ⟨_, ⟨g, rfl⟩, _, ⟨a, rfl⟩, rfl⟩
    refine ⟨g * (φ a) g⁻¹, ⟨g, a, rfl⟩, ?_⟩
    exact (SemidirectProduct.commutator_inl_inr (φ := φ) g a).symm

/-- Restricted-action version of `actionCommutator_map_inl`.

If `B` acts on `G` through `i : B →* A` and `φ : A →* MulAut G`, then the
`B`-action commutator maps into the same semidirect product `G ⋊[φ] A` as the
commutator of `inl(G)` with the image of `B` inside `inr(A)`. -/
theorem actionCommutator_map_inl_comp
    {A B G : Type*} [Group A] [Group B] [Group G]
    (φ : A →* MulAut G) (i : B →* A) :
    (actionCommutator (φ.comp i)).map (SemidirectProduct.inl : G →* G ⋊[φ] A) =
      ⁅(SemidirectProduct.inl : G →* G ⋊[φ] A).range,
        ((SemidirectProduct.inr : A →* G ⋊[φ] A).comp i).range⁆ := by
  rw [actionCommutator, MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨g, b, rfl⟩, rfl⟩
    refine ⟨SemidirectProduct.inl g, ⟨g, rfl⟩,
      SemidirectProduct.inr (i b), ⟨b, rfl⟩, ?_⟩
    exact SemidirectProduct.commutator_inl_inr (φ := φ) g (i b)
  · rintro ⟨_, ⟨g, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    refine ⟨g * (φ (i b)) g⁻¹, ⟨g, b, rfl⟩, ?_⟩
    exact (SemidirectProduct.commutator_inl_inr (φ := φ) g (i b)).symm

                                                                          
                                
                                                 
                                           
                                                              
                                            
                          
                                                 

                                                                               
                                                                                        
                           
                                                                                     
                                                    
                                                                                           
                                  
                                                                       
         
       
             
                                         
                                                 
                              
                          
                                                                                               
                                                                      
             
         
                                   
                                 
                                                                                                    
                                                
                              
                          
                              
                                                                                        
                                           
                                          
             
         

                                                                                        
                                               
                                                                                        
                                                    
                                 
                                                                                         
                                                   
       
                                                                              
             
                            
                                    
                                                                   
                                                                             
                                                        
                                    
                         
                                                                                                
                                           
                        
         

/-- **`actionCommutator φ` は G で normal subgroup**.

経路: `actionCommutator_map_inl` で `(actionCommutator φ).map inl = ⁅inl.range, inr.range⁆`,
Γ 内で `inl.range ⊔ inr.range = ⊤` (`SemidirectProduct.inl_range_sup_inr_range_eq_top`) より
Lem 4.1 系 `commutator_normal_of_sup_eq_top` で `⁅inl.range, inr.range⁆.Normal`. `inl`
injectivity で pull back (`Subgroup.Normal.of_map_injective`).

Isaacs §4C 冒頭注 (Lem 4.1 を Γ で適用) を直接実装. -/
instance actionCommutator.normal {A G : Type*} [Group A] [Group G] (φ : A →* MulAut G) :
    (actionCommutator φ).Normal := by
  refine Subgroup.Normal.of_map_injective
    (φ := (SemidirectProduct.inl : G →* G ⋊[φ] A)) SemidirectProduct.inl_injective ?_
  rw [actionCommutator_map_inl]
  exact commutator_normal_of_sup_eq_top SemidirectProduct.inl_range_sup_inr_range_eq_top

/-! ### Isaacs §4C: [G,A] の universal property (Lem 4.20, Cor 4.21) -/

/-- **Isaacs Lemma 4.20** (element form, right): `actionCommutator φ ≤ N` iff
`∀ a g, (φ a) g * g⁻¹ ∈ N`. つまり `actionCommutator φ` は
`{(φ a) g * g⁻¹ : a g}` で生成される最小の部分群.

**意味**: `N ⊴ G` が `A`-不変なら `actionCommutator ≤ N ↔ A acts trivially on G/N`
(右剰余類 `Nx` が A 不変 ↔ `(φ a) x ∈ Nx`).

**証明**: `actionCommutator` は `g * (φ a) g⁻¹ = ((φ a) g * g⁻¹)⁻¹` で生成されるので
`(φ a) g * g⁻¹` の集合と同じ subgroup を生成する. -/
theorem actionCommutator_le_iff {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (N : Subgroup G) :
    actionCommutator φ ≤ N ↔ ∀ a : A, ∀ g : G, (φ a) g * g⁻¹ ∈ N := by
  constructor
  · intro h a g
    have h_gen : g * (φ a) g⁻¹ ∈ actionCommutator φ :=
      Subgroup.subset_closure ⟨g, a, rfl⟩
    have h_inv : (φ a) g * g⁻¹ = (g * (φ a) g⁻¹)⁻¹ := by
      rw [show (φ a) g⁻¹ = ((φ a) g)⁻¹ from map_inv (φ a) g]
      group
    rw [h_inv]
    exact Subgroup.inv_mem _ (h h_gen)
  · intro h
    rw [actionCommutator, Subgroup.closure_le]
    rintro _ ⟨g, a, rfl⟩
    have h_form : g * (φ a) g⁻¹ = ((φ a) g * g⁻¹)⁻¹ := by
      rw [show (φ a) g⁻¹ = ((φ a) g)⁻¹ from map_inv (φ a) g]
      group
    rw [h_form]
    exact Subgroup.inv_mem _ (h a g)

/-- **Isaacs Lemma 4.20** (element form, left): `actionCommutator φ ≤ N` iff
`∀ a g, g⁻¹ * (φ a) g ∈ N`. 左剰余類 `xN` 形.

**意味**: 左剰余類 `xN` が `A` 不変 ↔ `(φ a) x ∈ xN` ↔ `x⁻¹ * (φ a) x ∈ N`. -/
theorem actionCommutator_le_iff_left {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (N : Subgroup G) :
    actionCommutator φ ≤ N ↔ ∀ a : A, ∀ g : G, g⁻¹ * (φ a) g ∈ N := by
  rw [actionCommutator_le_iff]
  -- ∀ a g, (φ a) g * g⁻¹ ∈ N ↔ ∀ a g, g⁻¹ * (φ a) g ∈ N
  constructor
  · intro h a x
    have h' := h a x⁻¹
    rw [show (φ a) x⁻¹ = ((φ a) x)⁻¹ from map_inv (φ a) x] at h'
    -- h' : ((φ a) x)⁻¹ * x⁻¹⁻¹ ∈ N
    have h_eq : ((φ a) x)⁻¹ * x⁻¹⁻¹ = (x⁻¹ * (φ a) x)⁻¹ := by group
    rw [h_eq] at h'
    simpa using Subgroup.inv_mem _ h'
  · intro h a x
    have h' := h a x⁻¹
    rw [show (φ a) x⁻¹ = ((φ a) x)⁻¹ from map_inv (φ a) x] at h'
    have h_eq : x⁻¹⁻¹ * ((φ a) x)⁻¹ = ((φ a) x * x⁻¹)⁻¹ := by group
    rw [h_eq] at h'
    simpa using Subgroup.inv_mem _ h'

/-- `actionCommutator φ = ⊥` iff `A` acts trivially on `G` (`∀ a g, (φ a) g = g`).

Lem 4.20 left form を `N = ⊥` で特殊化. BaerMul wrapper への翻訳に基本. -/
theorem actionCommutator_eq_bot_iff_acts_trivially {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) :
    actionCommutator φ = ⊥ ↔ ∀ a : A, ∀ g : G, (φ a) g = g := by
  rw [eq_bot_iff, actionCommutator_le_iff_left]
  refine ⟨fun h a g => ?_, fun h a g => ?_⟩
  · have hg := h a g
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hg
    exact hg.symm
  · rw [Subgroup.mem_bot, h a g, inv_mul_cancel]

/-- **A-不変部分群への作用制限**: `φ : A →* MulAut G` + `IsAInvariant φ H` から
`A →* MulAut ↥H` を構成. 関数本体は `(φ a)` を `H` に制限したもの.

Thm 4.36 induction で IH を `[G, A] < G` 等の subgroup に適用するために必要. -/
def OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom {A G : Type*} [Group A] [Group G]
    {φ : A →* MulAut G} {H : Subgroup G}
    (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) : A →* MulAut H where
  toFun a := {
    toFun := fun h => ⟨(φ a) h.val, hH.smul_mem a h.property⟩
    invFun := fun h => ⟨(φ a)⁻¹ h.val, hH.inv_smul_mem a h.property⟩
    left_inv := fun h => Subtype.ext (by
      show (φ a)⁻¹ ((φ a) h.val) = h.val
      simp)
    right_inv := fun h => Subtype.ext (by
      show (φ a) ((φ a)⁻¹ h.val) = h.val
      simp)
    map_mul' := fun x y => Subtype.ext (map_mul (φ a) x.val y.val)
  }
  map_one' := by
    ext h
    show ((φ 1 : MulAut G) h.val) = h.val
    simp
  map_mul' a b := by
    ext h
    show ((φ (a * b) : MulAut G) h.val) = ((φ a) ((φ b) h.val))
    rw [map_mul]; rfl

@[simp] lemma OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom_apply_val
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G} {H : Subgroup G}
    (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H) (a : A) (h : H) :
    ((OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH a) h).val =
      (φ a) h.val := rfl

/-- If `H` is A-invariant and `K` is characteristic in `H`, then the image of `K`
inside `G` is A-invariant. -/
theorem _root_.OddOrder.Isaacs.Ch03.IsAInvariant.map_subtype_of_characteristic
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {H : Subgroup G} (hH : OddOrder.Isaacs.Ch03.IsAInvariant φ H)
    {K : Subgroup H} [K.Characteristic] :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (K.map H.subtype) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a x hx
  rcases hx with ⟨k, hk, rfl⟩
  let ψ : A →* MulAut H := OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH
  have hK_map : K.map (ψ a).toMonoidHom = K :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) (ψ a)
  have hk' : (ψ a) k ∈ K := by
    have : (ψ a) k ∈ K.map (ψ a).toMonoidHom := ⟨k, hk, rfl⟩
    rwa [hK_map] at this
  exact ⟨(ψ a) k, hk', rfl⟩

/-- **A-不変正規部分群で割った商群への誘導作用**.

`N` が `φ` で不変なら, 各 `φ a` は `G/N` の自己同型を誘導する. -/
noncomputable def _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) : A →* MulAut (G ⧸ N) where
  toFun a := QuotientGroup.congr N N (φ a) (by
    change N.map (φ a).toMonoidHom = N
    exact hN a)
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro g
    simp
  map_mul' a b := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro g
    simp [map_mul]

@[simp] lemma _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk'
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) (a : A) (g : G) :
    (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN a)
        (QuotientGroup.mk' N g) =
      QuotientGroup.mk' N ((φ a) g) := rfl

@[simp] lemma _root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) (a : A) (g : G) :
    (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN a) (g : G ⧸ N) =
      ((φ a) g : G ⧸ N) := rfl

/- Note (issue 0106): `quotientMulAutHom` and its two `simp` lemmas were originally declared with
a qualified head *inside* `namespace OddOrder.Isaacs.Ch04`, yielding the doubled real name
`OddOrder.Isaacs.Ch04.OddOrder.Isaacs.Ch03.…`.  They now live at the intended single namespace
(`_root_.` head above).  No deprecated aliases are kept: alias constants under the doubled name
would make every qualified reference ambiguous in files that `open OddOrder.Isaacs.Ch04`
file-wide.  Downstream consumers of the old doubled name: drop the `OddOrder.Isaacs.Ch04.`
prefix. -/

                                                                                   
                                                                                          
                                                                                
                                                    
                                                                                  
                                                                                          
                                                                               
                                                                                                  
                                                                       
                          
               
                                                           
                                               
                                                                
             
                      
                                                                               
                                                                                  
                                                                           
                                                                                           
                                                                                        
                                                                                
                            
                                      
              
                                               
                                                             
           
                                                                                   

                                                                 
                          
                                                             
                                                            
                               
                                                 
                                                                    
                                     
                                                                     
                                         
                                                     
              
                                 
                               
                                         
                                                                                

                                                                         
                                   
                                                               
                                                            
                               
                                                 
                            
                                           
                                                                          
                                                                              
                                                     
              
                                   
                                                                               
                        

                                                                   

                                                                    
                                                                           
                                                                       
                                                
                                                 
                               
                                                              
                                                  
                                                                           
                                                          
                       
                                                            
                                                      
                                                  
                                               
                                    
                                 
                                                                        
               
                       
                         
                           
                             
                                          
                                                                            
               
                      

/-- The action commutator descends to quotients as the image of the action commutator. -/
theorem actionCommutator_quotient_eq_map
    {A G : Type*} [Group A] [Group G] {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hN : OddOrder.Isaacs.Ch03.IsAInvariant φ N) :
    actionCommutator (_root_.OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN) =
      (actionCommutator φ).map (QuotientGroup.mk' N) := by
  rw [actionCommutator, actionCommutator, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨q, a, rfl⟩
    refine QuotientGroup.induction_on q ?_
    intro g
    refine ⟨g * (φ a) g⁻¹, ⟨g, a, rfl⟩, ?_⟩
    simp [map_mul]
  · rintro ⟨_, ⟨g, a, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk' N g, a, by simp [map_mul]⟩

                                                                     
                                              
                                                            
                               
                                                 
                                        
                                                                                                
                                                 
           
                                        
         
                                                                       
                       
                           
                                                               

                                                                                       
                                            
                                                            
                                                                  
                                                 
                                                                                
                                
                                                                 
                                                            
                                                  
                                                                                        
                                                                                            
            
                                                                                          
                                                          
                                                                               
                                                   
                       
                                                                              
                                                                                                   
               
                                                                                         
                
                           
         
                                       
         
                                                                  

                                                                           
                                                                            
                                                                           
                                

                                                                                                     
                                                                      
                                             
               
                                
                                                    
                                                          
                                                   
                                                        
             

                                                                                             
                                                                                             
                                                                       
                                                            
                                                         
                                                
                                                     
              
                                                                                 
                                                                                 
                                                            
           
                       

                                                                                    
                                                        

                                                                                         
                                                                                          
                               
                                                                                                                
                                           
                                                                                                   
                                                                                              
                               
                                                            
                                                            
                                                                        
                                                              
                                    
                                                                                       
                                                                                       
                                                                 
                                 
                                                                           
                               
                                                             
                                                                     
                                                    
                                                                                    
                                           
                                                         
                                            
                                       
                                                               
                                        
                                            
                                                                                          
                   
                                                                                                      
                                                     
                                                                                    
                          
                                                                      
                                  
                                            
                                                                                                             
                                                                           
                                                                                               
                                             
                                                   
                                                                                  
                                                        
                                                                           
                                               
                                 
                                                                                     
                                                                        
                                                    
                                          
                                                                       
                                                             
                                                                                            
                                                     

end
end OddOrder.Isaacs.Ch04
