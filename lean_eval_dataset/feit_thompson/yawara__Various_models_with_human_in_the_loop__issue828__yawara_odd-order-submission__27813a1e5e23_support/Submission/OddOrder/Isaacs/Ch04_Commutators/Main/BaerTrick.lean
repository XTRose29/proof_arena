import Submission.OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroupsCoprime

/-!
# Isaacs §4D 後半 — Baer trick (Lem 4.37) と応用 (pp. 141-146)

Split from the former monolithic `OddOrder.Isaacs.Ch04_Commutators.Main` (directory split, issue 0103).
-/
namespace OddOrder.Isaacs.Ch04
open scoped commutatorElement

variable {G : Type*} [Group G]

section /- 4D: Coprime action — Fitting + Thompson PxQ + Baer (pp. 138-146) -/

/-! ### Isaacs §4D: Baer trick (Lem 4.37) — odd order class ≤ 2 ⇒ additive group structure

For `G` finite of **odd order** and **nilpotence class ≤ 2**, define
`baerAdd x y := x * y * sqrtOdd ⁅y, x⁆`. Then `(G, baerAdd)` is an abelian group, and:
- (a) commuting elements satisfy `x +' y = x * y`.
- (b) Additive order = multiplicative order.
- (c) Every multiplicative automorphism is also an additive automorphism.

下流: Thm 4.36 (p > 2, p-群 + p'-A fixes order-p elements ⇒ A trivial) で利用. -/

/-- **Square root in groups with odd `Nat.card`**: `sqrtOdd x := x^((|G|+1)/2)`.
For `Odd (Nat.card G)`, `(sqrtOdd x)² = x` (`pow_card_eq_one'` で `x^(|G|+1) = x`). -/
noncomputable def sqrtOdd {G : Type*} [Group G] (x : G) : G :=
  x ^ ((Nat.card G + 1) / 2)

                                                 
                                                 

/-- **核補題**: `Odd (Nat.card G) ⇒ (sqrtOdd x)² = x`. -/
lemma sqrtOdd_sq {G : Type*} [Group G] (hOdd : Odd (Nat.card G)) (x : G) :
    (sqrtOdd x) ^ 2 = x := by
  unfold sqrtOdd
  rw [← pow_mul]
  have h_eq : (Nat.card G + 1) / 2 * 2 = Nat.card G + 1 := by
    obtain ⟨k, hk⟩ := hOdd; rw [hk]; omega
  rw [h_eq, pow_succ, pow_card_eq_one', one_mul]

@[simp] lemma sqrtOdd_one {G : Type*} [Group G] : sqrtOdd (1 : G) = 1 := by
  simp [sqrtOdd]

lemma sqrtOdd_inv {G : Type*} [Group G] (x : G) : sqrtOdd x⁻¹ = (sqrtOdd x)⁻¹ := by
  unfold sqrtOdd; rw [← inv_pow]

lemma sqrtOdd_mul_of_commute {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    sqrtOdd (x * y) = sqrtOdd x * sqrtOdd y := by
  unfold sqrtOdd; rw [Commute.mul_pow h]

lemma sqrtOdd_mem_subgroup {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    sqrtOdd x ∈ H := H.pow_mem hx _

                                      
                                                                                       
                                                              

                                                                                       
                                                                       
                                                                           
                                       
                
              

                                                      
                                                              
                                                            
                            

/-- **Baer addition** for class ≤ 2 odd order groups: `x +' y := x * y * sqrtOdd ⁅y, x⁆`. -/
noncomputable def baerAdd {G : Type*} [Group G] (x y : G) : G := x * y * sqrtOdd ⁅y, x⁆

lemma baerAdd_def {G : Type*} [Group G] (x y : G) :
    baerAdd x y = x * y * sqrtOdd ⁅y, x⁆ := rfl

/-- **Lem 4.37 part (a) precursor**: If `x` and `y` commute, then `x +' y = x * y`
(since `⁅y, x⁆ = 1` and `sqrtOdd 1 = 1`). -/
lemma baerAdd_eq_mul_of_commute {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    baerAdd x y = x * y := by
  rw [baerAdd_def, (commutatorElement_eq_one_iff_commute (g₁ := y) (g₂ := x)).mpr h.symm,
      sqrtOdd_one, mul_one]

/-- Identity: `1 +' x = x`. -/
@[simp] lemma baerAdd_one_left {G : Type*} [Group G] (x : G) : baerAdd 1 x = x := by
  rw [baerAdd_def, one_mul, commutatorElement_one_right, sqrtOdd_one, mul_one]

/-- Identity: `x +' 1 = x`. -/
@[simp] lemma baerAdd_one_right {G : Type*} [Group G] (x : G) : baerAdd x 1 = x := by
  rw [baerAdd_def, mul_one, commutatorElement_one_left, sqrtOdd_one, mul_one]

/-- Inverse: `x +' x⁻¹ = 1`. -/
@[simp] lemma baerAdd_inv_right {G : Type*} [Group G] (x : G) : baerAdd x x⁻¹ = 1 := by
  have h1 : ⁅x⁻¹, x⁆ = (1 : G) :=
    commutatorElement_eq_one_iff_commute.mpr (Commute.refl x).inv_left
  rw [baerAdd_def, mul_inv_cancel, h1, sqrtOdd_one, mul_one]

/-- Inverse: `x⁻¹ +' x = 1`. -/
@[simp] lemma baerAdd_inv_left {G : Type*} [Group G] (x : G) : baerAdd x⁻¹ x = 1 := by
  have h1 : ⁅x, x⁻¹⁆ = (1 : G) :=
    commutatorElement_eq_one_iff_commute.mpr (Commute.refl x).inv_right
  rw [baerAdd_def, inv_mul_cancel, h1, sqrtOdd_one, mul_one]

/-- **Lem 4.37 commutativity**: `x +' y = y +' x` for class ≤ 2.

Derivation: `y +' x = y * x * sqrtOdd ⁅x, y⁆ = x * y * ⁅y, x⁆ * sqrtOdd ⁅x, y⁆`
(using `mul_comm_commutator_of_class_le_two`). Now `⁅x, y⁆⁻¹ = ⁅y, x⁆`, so
`sqrtOdd ⁅x, y⁆ = (sqrtOdd ⁅y, x⁆)⁻¹`. Combined:
`y +' x = x * y * ⁅y, x⁆ * (sqrtOdd ⁅y, x⁆)⁻¹ = x * y * sqrtOdd ⁅y, x⁆ = x +' y`
(using `(sqrtOdd ⁅y, x⁆)² = ⁅y, x⁆`). -/
lemma baerAdd_comm {G : Type*} [Group G] (hC : _root_.commutator G ≤ Subgroup.center G)
    (hOdd : Odd (Nat.card G)) (x y : G) :
    baerAdd x y = baerAdd y x := by
  rw [baerAdd_def, baerAdd_def]
  -- Set S := sqrtOdd ⁅y, x⁆. Show x * y * S = y * x * sqrtOdd ⁅x, y⁆.
  set S : G := sqrtOdd ⁅y, x⁆ with hS_def
  have h_yx : y * x = x * y * ⁅y, x⁆ := mul_comm_commutator_of_class_le_two hC x y
  have h_inv : (sqrtOdd ⁅x, y⁆ : G) = S⁻¹ := by
    rw [hS_def, ← sqrtOdd_inv]
    congr 1
    exact (commutatorElement_inv y x).symm
  have h_sq : S * S = ⁅y, x⁆ := by
    have := sqrtOdd_sq hOdd (⁅y, x⁆ : G); rw [sq] at this; exact this
  -- Goal: x * y * S = y * x * sqrtOdd ⁅x, y⁆
  rw [h_inv, h_yx]
  -- Goal: x * y * S = x * y * ⁅y, x⁆ * S⁻¹
  rw [← h_sq]
  -- Goal: x * y * S = x * y * (S * S) * S⁻¹
  group

                                                                       
                                                                                    
                                                      

/-- `sqrtOdd` of a central element is central. -/
lemma sqrtOdd_central_of_central {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) : sqrtOdd z ∈ Subgroup.center G :=
  sqrtOdd_mem_subgroup hz

/-- Right-hom version of commutator in class ≤ 2: `⁅z, a * b⁆ = ⁅z, a⁆ * ⁅z, b⁆`.
Derived from left-hom + `commutatorElement_inv`. -/
lemma commutatorElement_mul_right_of_class_le_two {G : Type*} [Group G]
    (hC : _root_.commutator G ≤ Subgroup.center G) (z a b : G) :
    ⁅z, a * b⁆ = ⁅z, a⁆ * ⁅z, b⁆ := by
  -- ⁅z, a*b⁆ = ⁅a*b, z⁆⁻¹ = (⁅a, z⁆ * ⁅b, z⁆)⁻¹ = ⁅b, z⁆⁻¹ * ⁅a, z⁆⁻¹ = ⁅z, b⁆ * ⁅z, a⁆
  -- In class 2, ⁅z, a⁆ and ⁅z, b⁆ are central, so commute.
  have h_swap : (⁅z, a⁆ : G) * ⁅z, b⁆ = ⁅z, b⁆ * ⁅z, a⁆ := by
    have h_ca : ⁅z, a⁆ ∈ Subgroup.center G := hC (commutatorElement_mem_commutator_top z a)
    exact (Subgroup.mem_center_iff.mp h_ca _).symm
  have h_inv_ab : (⁅a * b, z⁆ : G)⁻¹ = ⁅z, a * b⁆ := commutatorElement_inv (a * b) z
  have h_left : (⁅a * b, z⁆ : G) = ⁅a, z⁆ * ⁅b, z⁆ :=
    commutatorElement_mul_left_of_class_le_two hC a b z
  rw [← h_inv_ab, h_left, mul_inv_rev, commutatorElement_inv, commutatorElement_inv, h_swap]

/-- **Lem 4.37 associativity**: `x +' (y +' z) = (x +' y) +' z` for class ≤ 2 + odd order.

**証明**: 両辺は `x * y * z * sqrtOdd ⁅z, y⁆ * sqrtOdd ⁅y, x⁆ * sqrtOdd ⁅z, x⁆` に等しい
(中心 commutators の積 は順序自由).

LHS = `x * (yz·S_{zy}) * S_{(yz·S_{zy}, x)}`:
- `⁅yz·S_{zy}, x⁆ = ⁅y, x⁆ * ⁅z, x⁆` (left hom + `⁅S_{zy}, x⁆ = 1`)
- `S_{⁅y,x⁆·⁅z,x⁆} = S_{y,x} * S_{z,x}` (sqrtOdd of central commuting product)

RHS = `(xy·S_{yx}) * z * S_{(z, xy·S_{yx})}`:
- `⁅z, xy·S_{yx}⁆ = ⁅z, x⁆ * ⁅z, y⁆` (right hom + `⁅z, S_{yx}⁆ = 1`)
- `z` moves past central `S_{yx}` ⇒ `xyz·S_{yx}·S_{⁅z,x⁆·⁅z,y⁆}`
- `S_{⁅z,x⁆·⁅z,y⁆} = S_{z,x} * S_{z,y}`. -/
lemma baerAdd_assoc {G : Type*} [Group G] (hC : _root_.commutator G ≤ Subgroup.center G)
    (x y z : G) :
    baerAdd x (baerAdd y z) = baerAdd (baerAdd x y) z := by
  -- Notation: S_{ab} = sqrtOdd ⁅a, b⁆
  set Syz : G := sqrtOdd ⁅z, y⁆
  set Sxy : G := sqrtOdd ⁅y, x⁆
  set Sxz : G := sqrtOdd ⁅z, x⁆
  -- Centrality of all sqrtOdd-of-commutator elements
  have h_Sc_zy : Syz ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top z y))
  have h_Sc_yx : Sxy ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top y x))
  have h_Sc_zx : Sxz ∈ Subgroup.center G :=
    sqrtOdd_central_of_central (hC (commutatorElement_mem_commutator_top z x))
  -- Helper: central element commutes with anything (Commute)
  have h_comm_central : ∀ {c : G}, c ∈ Subgroup.center G → ∀ a, Commute c a := fun hc a =>
    (Subgroup.mem_center_iff.mp hc a).symm
  have h_Comm_Syz : ∀ a, Commute Syz a := fun a => h_comm_central h_Sc_zy a
  have h_Comm_Sxy : ∀ a, Commute Sxy a := fun a => h_comm_central h_Sc_yx a
  -- LHS commutator computation: ⁅y * z * Syz, x⁆ = ⁅y, x⁆ * ⁅z, x⁆
  have h_LHS_arg : ⁅y * z * Syz, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := by
    have h_yz_x : ⁅y * z, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ :=
      commutatorElement_mul_left_of_class_le_two hC y z x
    have h_Syz_x : ⁅Syz, x⁆ = (1 : G) :=
      (commutatorElement_eq_one_iff_commute (g₁ := Syz) (g₂ := x)).mpr (h_Comm_Syz x)
    rw [commutatorElement_mul_left_of_class_le_two hC, h_yz_x, h_Syz_x, mul_one]
  -- RHS commutator computation: ⁅z, x * y * Sxy⁆ = ⁅z, x⁆ * ⁅z, y⁆
  have h_RHS_arg : ⁅z, x * y * Sxy⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
    have h_z_xy : ⁅z, x * y⁆ = ⁅z, x⁆ * ⁅z, y⁆ :=
      commutatorElement_mul_right_of_class_le_two hC z x y
    have h_z_Sxy : ⁅z, Sxy⁆ = (1 : G) :=
      (commutatorElement_eq_one_iff_commute (g₁ := z) (g₂ := Sxy)).mpr (h_Comm_Sxy z).symm
    rw [commutatorElement_mul_right_of_class_le_two hC z (x * y) Sxy, h_z_xy, h_z_Sxy, mul_one]
  -- Distribute sqrtOdd over products of central commutators
  -- sqrtOdd (⁅y, x⁆ * ⁅z, x⁆) = Sxy * Sxz (centrals commute)
  have h_C_xy : (⁅y, x⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top y x)
  have h_C_zx : (⁅z, x⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top z x)
  have h_split_LHS : sqrtOdd (⁅y, x⁆ * ⁅z, x⁆ : G) = Sxy * Sxz :=
    sqrtOdd_mul_of_commute ((h_comm_central h_C_xy) ⁅z, x⁆)
  -- sqrtOdd (⁅z, x⁆ * ⁅z, y⁆) = Sxz * Syz
  have h_C_zy : (⁅z, y⁆ : G) ∈ Subgroup.center G :=
    hC (commutatorElement_mem_commutator_top z y)
  have h_split_RHS : sqrtOdd (⁅z, x⁆ * ⁅z, y⁆ : G) = Sxz * Syz :=
    sqrtOdd_mul_of_commute ((h_comm_central h_C_zx) ⁅z, y⁆)
  -- Compute LHS and RHS
  -- LHS = x * (y * z * Syz) * sqrtOdd ⁅y * z * Syz, x⁆
  --     = x * y * z * Syz * sqrtOdd (⁅y, x⁆ * ⁅z, x⁆)
  --     = x * y * z * Syz * Sxy * Sxz
  -- RHS = (x * y * Sxy) * z * sqrtOdd ⁅z, x * y * Sxy⁆
  --     = x * y * Sxy * z * sqrtOdd (⁅z, x⁆ * ⁅z, y⁆)
  --     = x * y * Sxy * z * Sxz * Syz
  --     = x * y * z * Sxy * Sxz * Syz  (Sxy commutes with z)
  -- LHS = RHS iff Syz * Sxy * Sxz = Sxy * Sxz * Syz, which holds because all centrals commute.
  rw [baerAdd_def, baerAdd_def, baerAdd_def, baerAdd_def, h_LHS_arg, h_RHS_arg,
      h_split_LHS, h_split_RHS]
  -- Goal: x * (y * z * Syz) * (Sxy * Sxz) = (x * y * Sxy) * z * (Sxz * Syz)
  -- Both sides normalize to `x * y * z * Sxy * Sxz * Syz` via commutativity
  -- of central elements (Syz, Sxy, Sxz).
  have h_Sxy_z := h_Comm_Sxy z
  have h_LHS_norm :
      x * (y * z * Syz) * (Sxy * Sxz) = x * y * z * Sxy * Sxz * Syz := by
    have hC : Commute Syz (Sxy * Sxz) := (h_Comm_Syz Sxy).mul_right (h_Comm_Syz Sxz)
    have h_rearrange :
        x * (y * z * Syz) * (Sxy * Sxz) = (x * y * z) * (Syz * (Sxy * Sxz)) := by group
    rw [h_rearrange, hC.eq]; group
  have h_RHS_norm :
      (x * y * Sxy) * z * (Sxz * Syz) = x * y * z * Sxy * Sxz * Syz := by
    have h_rearrange :
        (x * y * Sxy) * z * (Sxz * Syz) = x * y * (Sxy * z) * (Sxz * Syz) := by group
    rw [h_rearrange, h_Sxy_z.eq]; group
  rw [h_LHS_norm, h_RHS_norm]

/-- **Lem 4.37 part (c)**: Every group homomorphism (between equal-card groups) preserves
`baerAdd`: `f (baerAdd x y) = baerAdd (f x) (f y)`. -/
lemma baerAdd_map_eq {G H : Type*} [Group G] [Group H] (f : G →* H)
    (h_card : Nat.card G = Nat.card H) (x y : G) :
    f (baerAdd x y) = baerAdd (f x) (f y) := by
  rw [baerAdd_def, baerAdd_def, map_mul, map_mul]
  congr 1
  -- f (sqrtOdd ⁅y, x⁆) = sqrtOdd (f ⁅y, x⁆) = sqrtOdd ⁅f y, f x⁆
  rw [sqrtOdd, sqrtOdd, h_card, map_pow, map_commutatorElement]

/-- **Lem 4.37 part (c) for MulEquiv** (Aut preservation): For `f : G ≃* G`,
`f (baerAdd x y) = baerAdd (f x) (f y)`. つまり multiplicative automorphism は
baerAdd を保存. -/
lemma baerAdd_mulEquiv_eq {G : Type*} [Group G] (f : G ≃* G) (x y : G) :
    f (baerAdd x y) = baerAdd (f x) (f y) :=
  baerAdd_map_eq f.toMonoidHom rfl x y

/-! ### Lem 4.37(b) element form + `BaerMul G` 型ラッパー (CommGroup 構造)

Baer trick の "additive group" は実際には Lean 上では type wrapper 経由で実装する.
`BaerMul G := G` (定義的に同型) に `CommGroup` インスタンスを `baerAdd` で与える.
これにより Cor 4.35 (CommGroup 仮定) を そのまま `BaerMul G` に適用できる.

教科書 (Isaacs p.142) (b) 証明の鍵: `nx = x + (n-1)x = x · x^(n-1) = x^n`
(commute case で `baerAdd_eq_mul_of_commute`). 実装では `npow x n := x^n` (G の冪) を直接採用し,
`npow_succ : npow (n+1) x = baerAdd (npow n x) x` を `baerAdd_pow_self_eq_pow_succ` で提供. -/

/-- **Lem 4.37(b) inductive step** (仮定不要): `baerAdd (x^n) x = x^(n+1)`.

`x` と `x^n` は常に commute するので, `baerAdd x^n x = x^n * x * sqrtOdd ⁅x, x^n⁆ = x^n · x · 1 = x^{n+1}`.
これが `BaerMul G` の `npow_succ` フィールドに対応する. -/
lemma baerAdd_pow_self_eq_pow_succ {G : Type*} [Group G] (x : G) (n : ℕ) :
    baerAdd (x ^ n) x = x ^ (n + 1) := by
  have h_comm : Commute (x ^ n) x := Commute.pow_self x n
  rw [baerAdd_eq_mul_of_commute h_comm, ← pow_succ]

/-- **Baer trick type wrapper**: `BaerMul G := G` (定義的に同型).

`G` が奇数位数 + class ≤ 2 のときに `BaerMul G` 上に `baerAdd` を乗法とする `CommGroup` 構造を
与える (Lem 4.37). これにより mathlib の CommGroup 用 API (Cor 4.35 等) を `BaerMul G` に
直接適用できる.

Naming: 乗法的 wrapper として扱う ("multiplicative view of (G, +')"). -/
def BaerMul (G : Type*) : Type _ := G

namespace BaerMul

variable {G : Type*}

/-- Coercion `BaerMul G ≃ G` (identity at runtime). -/
def toG : BaerMul G ≃ G := Equiv.refl _

/-- Coercion `G ≃ BaerMul G` (identity at runtime). -/
def ofG : G ≃ BaerMul G := Equiv.refl _

@[simp] theorem toG_ofG (x : G) : toG (ofG x) = x := rfl
@[simp] theorem ofG_toG (x : BaerMul G) : ofG (toG x) = x := rfl

end BaerMul

/-- `Mul (BaerMul G) = baerAdd`. -/
noncomputable instance BaerMul.instMul {G : Type*} [Group G] : Mul (BaerMul G) where
  mul x y := BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y))

/-- `1 : BaerMul G = ofG 1`. -/
instance BaerMul.instOne {G : Type*} [One G] : One (BaerMul G) where
  one := BaerMul.ofG 1

/-- `(·)⁻¹ : BaerMul G → BaerMul G` is the same as G's inverse (Lem 4.37 で `baerAdd x⁻¹ x = 1`). -/
instance BaerMul.instInv {G : Type*} [Inv G] : Inv (BaerMul G) where
  inv x := BaerMul.ofG (BaerMul.toG x)⁻¹

/-- **CommGroup instance for `BaerMul G`**: `G` が `Odd (Nat.card G)` + `commutator G ≤ Z(G)`
を満たすとき, `(BaerMul G, baerAdd, 1, ·⁻¹)` は可換群.

実装方針: 基本 `Mul / One / Inv` instance を別途与えて, ここでは **axiom フィールドのみ提供**.
`npow / zpow` フィールドはデフォルト (`npowRec` / `zpowRec`) を使用. `npowRec` は `*`
(我々の baerAdd) を `n` 回反復するので, BaerMul の pow = `baerAdd`-iterate.
G の `x^n` との一致は Lem 4.37(b) (`baerAdd_pow_self_eq_pow_succ`) 経由で別途証明. -/
noncomputable instance BaerMul.instCommGroup {G : Type*} [Group G]
    [hOdd : Fact (Odd (Nat.card G))]
    [hC : Fact (_root_.commutator G ≤ Subgroup.center G)] : CommGroup (BaerMul G) where
  mul_assoc x y z := by
    show BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y))))
        (BaerMul.toG z)) =
      BaerMul.ofG (baerAdd (BaerMul.toG x)
        (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG y) (BaerMul.toG z)))))
    simp only [BaerMul.toG_ofG]
    exact congr_arg BaerMul.ofG
      (baerAdd_assoc hC.out (BaerMul.toG x) (BaerMul.toG y) (BaerMul.toG z)).symm
  one_mul x := by
    show BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG 1)) (BaerMul.toG x)) = x
    simp only [BaerMul.toG_ofG, baerAdd_one_left]
    rfl
  mul_one x := by
    show BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG (BaerMul.ofG 1))) = x
    simp only [BaerMul.toG_ofG, baerAdd_one_right]
    rfl
  mul_comm x y := by
    show BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y)) =
      BaerMul.ofG (baerAdd (BaerMul.toG y) (BaerMul.toG x))
    exact congr_arg BaerMul.ofG (baerAdd_comm hC.out hOdd.out _ _)
  inv_mul_cancel x := by
    show BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (BaerMul.toG x)⁻¹)) (BaerMul.toG x)) =
      BaerMul.ofG 1
    simp only [BaerMul.toG_ofG]
    rw [baerAdd_inv_left]

instance BaerMul.instFinite {G : Type*} [Finite G] : Finite (BaerMul G) :=
  inferInstanceAs (Finite G)

@[simp] lemma BaerMul.nat_card_eq {G : Type*} : Nat.card (BaerMul G) = Nat.card G := rfl

/-- **Lem 4.37(c) wrapped**: G の multiplicative automorphism は `BaerMul G` 上でも
multiplicative automorphism (= baerAdd 保存). 関数本体は同じ (恒等経由). -/
noncomputable def MulAut.toBaerMul {G : Type*} [Group G] (f : G ≃* G) :
    BaerMul G ≃* BaerMul G where
  toFun x := BaerMul.ofG (f (BaerMul.toG x))
  invFun x := BaerMul.ofG (f.symm (BaerMul.toG x))
  left_inv x := by
    show BaerMul.ofG (f.symm (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG x))))) = x
    simp only [BaerMul.toG_ofG, f.symm_apply_apply]
    rfl
  right_inv x := by
    show BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (f.symm (BaerMul.toG x))))) = x
    simp only [BaerMul.toG_ofG, f.apply_symm_apply]
    rfl
  map_mul' x y := by
    show BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (baerAdd (BaerMul.toG x) (BaerMul.toG y))))) =
        BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG x))))
          (BaerMul.toG (BaerMul.ofG (f (BaerMul.toG y)))))
    simp only [BaerMul.toG_ofG]
    exact congr_arg BaerMul.ofG (baerAdd_mulEquiv_eq f (BaerMul.toG x) (BaerMul.toG y))

/-- `MulAut.toBaerMul` は群準同型 (composition / 1 を保存). 下の `MonoidHom.toBaerMulLift`
を構成するために使う. -/
noncomputable def MulAut.toBaerMulHom {G : Type*} [Group G] :
    MulAut G →* MulAut (BaerMul G) where
  toFun f := MulAut.toBaerMul f
  map_one' := by
    ext x
    show BaerMul.ofG ((1 : MulAut G) (BaerMul.toG x)) = x
    show BaerMul.ofG (BaerMul.toG x) = x
    exact BaerMul.ofG_toG x
  map_mul' f g := by
    ext x
    show BaerMul.ofG ((f * g) (BaerMul.toG x)) =
        BaerMul.ofG (f (BaerMul.toG (BaerMul.ofG (g (BaerMul.toG x)))))
    simp only [BaerMul.toG_ofG]
    rfl

/-- φ : A →* MulAut G を BaerMul G への作用 φ' : A →* MulAut (BaerMul G) に lift する.
関数本体は同じ (Lem 4.37(c)). -/
noncomputable def MonoidHom.toBaerMulLift {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) : A →* MulAut (BaerMul G) :=
  MulAut.toBaerMulHom.comp φ

@[simp] lemma MonoidHom.toBaerMulLift_apply {A G : Type*} [Group A] [Group G]
    (φ : A →* MulAut G) (a : A) (g : BaerMul G) :
    (MonoidHom.toBaerMulLift φ a) g = BaerMul.ofG ((φ a) (BaerMul.toG g)) := rfl

/-- **Lem 4.37(b) full form**: `BaerMul G` の自然冪 (baerAdd-iterate) = `G` の自然冪.
`npow_succ` の帰納で示す. -/
lemma BaerMul.npow_eq_pow {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)]
    (x : BaerMul G) (n : ℕ) :
    @HPow.hPow (BaerMul G) ℕ _ _ x n = BaerMul.ofG ((BaerMul.toG x) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    rfl
  | succ k ih =>
    rw [pow_succ, ih]
    show BaerMul.ofG (baerAdd (BaerMul.toG (BaerMul.ofG ((BaerMul.toG x) ^ k))) (BaerMul.toG x)) =
        BaerMul.ofG ((BaerMul.toG x) ^ (k + 1))
    simp only [BaerMul.toG_ofG]
    rw [baerAdd_pow_self_eq_pow_succ]

/-- `BaerMul G` での `x^n = 1` ↔ `G` での `x^n = 1`. Cor 4.35 適用時の `g^p = 1` 翻訳に使用. -/
lemma BaerMul.pow_eq_one_iff {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)]
    (x : BaerMul G) (n : ℕ) :
    @HPow.hPow (BaerMul G) ℕ _ _ x n = 1 ↔ (BaerMul.toG x) ^ n = 1 := by
  rw [BaerMul.npow_eq_pow]
  show BaerMul.ofG ((BaerMul.toG x) ^ n) = BaerMul.ofG 1 ↔ (BaerMul.toG x) ^ n = 1
  exact BaerMul.ofG.apply_eq_iff_eq

/-- `IsPGroup p (BaerMul G) ↔ IsPGroup p G`. BaerMul の構造を経由しても p-群性は不変. -/
lemma BaerMul.isPGroup_iff {G : Type*} [Group G]
    [Fact (Odd (Nat.card G))] [Fact (_root_.commutator G ≤ Subgroup.center G)] (p : ℕ) :
    IsPGroup p (BaerMul G) ↔ IsPGroup p G := by
  unfold IsPGroup
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨n, hn⟩ := h (BaerMul.ofG x)
    refine ⟨n, ?_⟩
    rw [BaerMul.pow_eq_one_iff] at hn
    simpa [BaerMul.toG_ofG] using hn
  · obtain ⟨n, hn⟩ := h (BaerMul.toG x)
    refine ⟨n, ?_⟩
    rw [BaerMul.pow_eq_one_iff]
    exact hn

/-- **系 of Lem 4.28**: `A` が `actionCommutator φ` (= `[G, A]`) 上で trivial 作用するとき,
coprime + (A or G solvable) 仮定下では `actionCommutator φ = ⊥` (= A trivial on whole G).

**証明**: Lem 4.28 で G = C_G(A) · [G, A]. 各 g = c * x で `c ∈ C_G(A)` ⇒ `(φ a) c = c`,
`x ∈ [G, A]` + 仮定 ⇒ `(φ a) x = x`. 故に `(φ a) g = (φ a)(c·x) = c·x = g`.

Thm 4.36 induction の `[G, A] < G` ケースで使用 (IH ⇒ A trivial on [G, A] ⇒ A trivial on G). -/
theorem actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : IsSolvable A ∨ IsSolvable G)
    (h_triv : ∀ a : A, ∀ h ∈ actionCommutator φ, (φ a) h = h) :
    actionCommutator φ = ⊥ := by
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a g
  have h_top : g ∈ Subgroup.fixedPointsOfMulAut φ ⊔ actionCommutator φ := by
    rw [fixedPoints_sup_actionCommutator_eq_top hCop hSolv]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup_of_normal_right] at h_top
  obtain ⟨c, hc_fix, x, hx_ac, h_eq⟩ := h_top
  -- h_eq : c * x = g, hc_fix : c ∈ fixedPoints, hx_ac : x ∈ actionCommutator
  rw [← h_eq, map_mul, hc_fix a, h_triv a x hx_ac]

/-- **Isaacs Thm 4.36 (class ≤ 2 case)** ⭐: A acts on p-群 G of class ≤ 2 (p > 2),
A is p'-group, A fixes every order-p element of G ⇒ A trivial on G.

Baer trick で `BaerMul G` を可換群として扱い, Cor 4.35 を適用. これが Thm 4.36 の核.

`hp_odd : p ≠ 2` から `Odd p` → `Odd (p^k)` → `Odd (Nat.card G)`. `hC : class ≤ 2` を
`Fact` 化して `BaerMul.instCommGroup` を呼び出し可能に. -/
theorem actionCommutator_eq_bot_of_pgroup_class_le_two_fixes_order_p
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (hC : _root_.commutator G ≤ Subgroup.center G)
    (φ : A →* MulAut G) (hG : IsPGroup p G) (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    actionCommutator φ = ⊥ := by
  -- Set up Fact (Odd (Nat.card G))
  have hOdd_p : Odd p := hp.out.odd_of_ne_two hp_odd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
  have hOdd_card : Odd (Nat.card G) := by rw [hk]; exact hOdd_p.pow
  haveI : Fact (Odd (Nat.card G)) := ⟨hOdd_card⟩
  haveI : Fact (_root_.commutator G ≤ Subgroup.center G) := ⟨hC⟩
  -- φ' : A →* MulAut (BaerMul G)
  set φ' : A →* MulAut (BaerMul G) := MonoidHom.toBaerMulLift φ with hφ'
  -- IsPGroup p (BaerMul G)
  have hG' : IsPGroup p (BaerMul G) := (BaerMul.isPGroup_iff p).mpr hG
  -- h_fix translated to BaerMul G
  have h_fix' : ∀ g : BaerMul G, g ^ p = 1 → ∀ a : A, (φ' a) g = g := by
    intro g hg a
    have hg_G : (BaerMul.toG g) ^ p = 1 := (BaerMul.pow_eq_one_iff g p).mp hg
    have h_fixed : (φ a) (BaerMul.toG g) = BaerMul.toG g := h_fix _ hg_G a
    show BaerMul.ofG ((φ a) (BaerMul.toG g)) = g
    rw [h_fixed]
    exact BaerMul.ofG_toG g
  -- Apply Cor 4.35 to BaerMul G
  have h_bot_baer : actionCommutator φ' = ⊥ :=
    actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p φ' hG' hA_p' h_fix'
  -- Translate back to G via iff
  rw [actionCommutator_eq_bot_iff_acts_trivially] at h_bot_baer
  rw [actionCommutator_eq_bot_iff_acts_trivially]
  intro a g
  have h_act := h_bot_baer a (BaerMul.ofG g)
  -- h_act : (φ' a) (ofG g) = ofG g
  -- Unfold φ': (φ' a) (ofG g) = ofG ((φ a) (toG (ofG g))) = ofG ((φ a) g)
  -- So: ofG ((φ a) g) = ofG g, hence (φ a) g = g by injectivity
  have h_eq : BaerMul.ofG ((φ a) g) = BaerMul.ofG g := by
    have hkey : (φ' a) (BaerMul.ofG g) = BaerMul.ofG ((φ a) g) := by
      show BaerMul.ofG ((φ a) (BaerMul.toG (BaerMul.ofG g))) = BaerMul.ofG ((φ a) g)
      rw [BaerMul.toG_ofG]
    rw [← hkey]
    exact h_act
  exact BaerMul.ofG.injective h_eq

/-- **強帰納法版** (`Nat.card G ≤ n` パラメータ化). Thm 4.36 本体の補助. -/
private theorem isaacs_thm_4_36_aux {A : Type*} [Group A] [Finite A]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2) (hA_p' : ¬ p ∣ Nat.card A) :
    ∀ n : ℕ, ∀ {G : Type*} [Group G] [Finite G]
    (φ : A →* MulAut G) (_ : IsPGroup p G)
    (_ : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g),
    Nat.card G ≤ n → actionCommutator φ = ⊥ := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ _ _ h_le
    exfalso
    have h_pos : 0 < Nat.card G := Nat.card_pos
    omega
  | succ m IH =>
    intro G _ _ φ hG h_fix h_le
    -- Case: |G| ≤ m, apply IH
    rcases Nat.lt_or_ge (Nat.card G) (m + 1) with h_lt | h_ge
    · exact IH φ hG h_fix (Nat.le_of_lt_succ h_lt)
    have h_card_G : Nat.card G = m + 1 := le_antisymm h_le h_ge
    -- Subcase: G trivial
    by_cases hG_triv : Nontrivial G
    swap
    · haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_triv
      rw [actionCommutator_eq_bot_iff_acts_trivially]
      intro a g
      exact Subsingleton.elim _ _
    -- G nontrivial setup
    have hCop : Nat.Coprime (Nat.card A) (Nat.card G) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := G)).mp hG
      rw [hk]
      exact (Nat.Coprime.pow_right k (Nat.coprime_comm.mp
        (Nat.Prime.coprime_iff_not_dvd hp.out |>.mpr hA_p')))
    haveI hG_nilp : Group.IsNilpotent G := hG.isNilpotent
    have hG_solv : IsSolvable G := IsNilpotent.to_isSolvable
    have hSolv : IsSolvable A ∨ IsSolvable G := Or.inr hG_solv
    -- 補助: H ≠ ⊤ + Finite G ⇒ Nat.card ↥H < Nat.card G
    have card_lt_of_ne_top : ∀ {H : Subgroup G}, H ≠ ⊤ → Nat.card ↥H < Nat.card G := by
      intro H h_ne
      have h_dvd : Nat.card ↥H ∣ Nat.card G :=
        ⟨H.index, by rw [mul_comm, H.index_mul_card]⟩
      have h_le' : Nat.card ↥H ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos h_dvd
      have h_ne' : Nat.card ↥H ≠ Nat.card G := fun heq =>
        h_ne (Subgroup.eq_top_of_card_eq _ heq)
      exact Nat.lt_of_le_of_ne h_le' h_ne'
    -- Case分け: [G, A] < ⊤ vs ⊤
    by_cases h_AC_top : actionCommutator φ = ⊤
    swap
    · -- [G, A] < ⊤: IH を actionCommutator に適用
      set H : Subgroup G := actionCommutator φ
      have hH_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ H :=
        OddOrder.Isaacs.Ch03.IsAInvariant.actionCommutator φ
      let φ_H : A →* MulAut ↥H :=
        OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hH_inv
      have h_H_card_lt : Nat.card ↥H < Nat.card G := card_lt_of_ne_top h_AC_top
      have hH_pgrp : IsPGroup p ↥H := hG.to_subgroup H
      have h_fix_H : ∀ h : ↥H, h ^ p = 1 → ∀ a : A, (φ_H a) h = h := by
        intro h hh_pow a
        apply Subtype.ext
        show (φ a) h.val = h.val
        apply h_fix
        have := congr_arg (Subtype.val : ↥H → G) hh_pow
        simpa using this
      have h_IH_H := IH φ_H hH_pgrp h_fix_H
        (Nat.le_of_lt_succ (h_H_card_lt.trans_le h_le))
      have h_triv : ∀ a : A, ∀ x ∈ H, (φ a) x = x := by
        intro a x hx
        rw [actionCommutator_eq_bot_iff_acts_trivially] at h_IH_H
        have := h_IH_H a ⟨x, hx⟩
        exact congr_arg Subtype.val this
      exact actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime hCop hSolv h_triv
    -- [G, A] = ⊤: G' < ⊤, IH を G' に適用, Three-subgroups で class ≤ 2
    -- G' = commutator G
    set G' : Subgroup G := commutator G with hG'_def
    have hG'_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.derivedSeries φ 1
    have h_G'_lt_top : G' < ⊤ := IsSolvable.commutator_lt_top_of_nontrivial G
    have h_G'_card_lt : Nat.card ↥G' < Nat.card G := card_lt_of_ne_top h_G'_lt_top.ne
    let φ_G' : A →* MulAut ↥G' :=
      OddOrder.Isaacs.Ch03.IsAInvariant.toMulAutHom hG'_inv
    have hG'_pgrp : IsPGroup p ↥G' := hG.to_subgroup G'
    have h_fix_G' : ∀ g' : ↥G', g' ^ p = 1 → ∀ a : A, (φ_G' a) g' = g' := by
      intro g' hg'_pow a
      apply Subtype.ext
      show (φ a) g'.val = g'.val
      apply h_fix
      have := congr_arg (Subtype.val : ↥G' → G) hg'_pow
      simpa using this
    have h_IH_G' := IH φ_G' hG'_pgrp h_fix_G'
      (Nat.le_of_lt_succ (h_G'_card_lt.trans_le h_le))
    have h_triv_G' : ∀ a : A, ∀ g' ∈ G', (φ a) g' = g' := by
      intro a g' hg'
      rw [actionCommutator_eq_bot_iff_acts_trivially] at h_IH_G'
      have := h_IH_G' a ⟨g', hg'⟩
      exact congr_arg Subtype.val this
    -- Three-subgroups in Γ で G' ⊆ Z(G) を導く
    have h_class_le_2 : commutator G ≤ Subgroup.center G := by
      -- Γ = G ⋊[φ] A. XG = inl(G), YA = inr(A), XG' = inl(G').
      set XG : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inl : G →* G ⋊[φ] A).range
      set YA : Subgroup (G ⋊[φ] A) := (SemidirectProduct.inr : A →* G ⋊[φ] A).range
      set XG' : Subgroup (G ⋊[φ] A) := G'.map (SemidirectProduct.inl : G →* G ⋊[φ] A)
      -- Step 1: ⁅XG', YA⁆ = ⊥ (h_triv_G' + generator computation)
      have h_G'_YA : ⁅XG', YA⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        rintro _ ⟨k, hk, rfl⟩ _ ⟨a, rfl⟩
        rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
        have h_fix' : (φ a) k = k := h_triv_G' a k hk
        rw [show (φ a) k⁻¹ = ((φ a) k)⁻¹ from map_inv (φ a) k, h_fix', mul_inv_cancel]
        exact map_one _
      -- Step 2: ⁅XG, XG'⁆ ≤ XG' (G' normal in G ⇒ inl の像でも保たれる)
      have h_GG'_le : ⁅XG, XG'⁆ ≤ XG' := by
        rw [Subgroup.commutator_le]
        rintro _ ⟨g, rfl⟩ _ ⟨k, hk, rfl⟩
        -- Goal: ⁅inl g, inl k⁆ ∈ XG' (= inl(G'))
        rw [show (⁅(SemidirectProduct.inl g : G ⋊[φ] A), SemidirectProduct.inl k⁆ :
            G ⋊[φ] A) = SemidirectProduct.inl ⁅g, k⁆ from by
          simp [commutatorElement_def, ← map_mul, ← map_inv]]
        refine ⟨⁅g, k⁆, ?_, rfl⟩
        -- Since G' is normal, both `g * k * g⁻¹` and `k⁻¹` lie in G'.
        have hG'_normal : G'.Normal := inferInstance
        have h_gkg : g * k * g⁻¹ ∈ G' := hG'_normal.conj_mem k hk g
        have h_inv : k⁻¹ ∈ G' := G'.inv_mem hk
        rw [commutatorElement_def]
        exact G'.mul_mem h_gkg h_inv
      -- h12: ⁅⁅XG, XG'⁆, YA⁆ ⊆ ⁅XG', YA⁆ = ⊥
      have h12 : ⁅⁅XG, XG'⁆, YA⁆ = ⊥ := by
        rw [eq_bot_iff]
        calc ⁅⁅XG, XG'⁆, YA⁆ ≤ ⁅XG', YA⁆ := Subgroup.commutator_mono h_GG'_le le_rfl
          _ = ⊥ := h_G'_YA
      -- h23: ⁅⁅XG', YA⁆, XG⁆ = ⁅⊥, XG⁆ = ⊥
      have h23 : ⁅⁅XG', YA⁆, XG⁆ = ⊥ := by
        rw [h_G'_YA]
        exact Subgroup.commutator_bot_left XG
      -- Three-subgroups: ⁅⁅YA, XG⁆, XG'⁆ = ⊥
      have h_three : ⁅⁅YA, XG⁆, XG'⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate h12 h23
      -- ⁅YA, XG⁆ = ⁅XG, YA⁆ = XG (since actionCommutator = ⊤)
      have h_XGYA_eq_XG : ⁅XG, YA⁆ = XG := by
        rw [← actionCommutator_map_inl φ, h_AC_top]
        exact (MonoidHom.range_eq_map _).symm
      have h_YAXG_eq_XG : ⁅YA, XG⁆ = XG := by
        rw [Subgroup.commutator_comm]; exact h_XGYA_eq_XG
      -- So ⁅XG, XG'⁆ = ⊥ in Γ
      have h_XG_XG'_bot : ⁅XG, XG'⁆ = ⊥ := h_YAXG_eq_XG ▸ h_three
      -- Translate back to G: ⁅⊤, G'⁆ = ⊥ ⇒ G' ⊆ Z(G)
      -- inl(⁅⊤, G'⁆) = ⁅inl(⊤), inl(G')⁆ = ⁅XG, XG'⁆ = ⊥, so ⁅⊤, G'⁆ = ⊥ by inl injective
      have h_top_G'_bot : ⁅(⊤ : Subgroup G), G'⁆ = ⊥ := by
        apply Subgroup.map_injective (f := (SemidirectProduct.inl : G →* G ⋊[φ] A))
          SemidirectProduct.inl_injective
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.map_bot]
        exact h_XG_XG'_bot
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h_top_G'_bot
      -- h_top_G'_bot : ⊤ ≤ G'.centralizer
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have := h_top_G'_bot (Subgroup.mem_top y)
      exact (this x hx).symm
    -- Apply class ≤ 2 case
    exact actionCommutator_eq_bot_of_pgroup_class_le_two_fixes_order_p
      hp_odd h_class_le_2 φ hG hA_p' h_fix

/-- **Isaacs Theorem 4.36** ⭐ (= BG Thm 1.11, **FT クリティカル**):
`p > 2`, `G` p-群, `A` p'-群 が `G` に作用. `A` が `G` の全 order-p 要素を fix するならば,
`A` は `G` 上 trivial に作用する (`actionCommutator φ = ⊥`).

**証明** (Isaacs p.142): 強帰納法 on `|G|`.
- 自明 G: 即座.
- `[G, A] < G`: IH を `actionCommutator` に適用 ⇒ A trivial on [G, A] ⇒ Lem 4.28 系で結論.
- `[G, A] = G`: `G' < G` (G nontrivial nilpotent solvable). IH を G' に適用 ⇒ A trivial on G'.
  Three-subgroups in Γ = G ⋊ A ([G', A] = 1, [G, G'] ⊆ G' から) ⇒ `[G, G'] = 1` ⇒ G' ⊆ Z(G)
  ⇒ class ≤ 2. Baer trick + Cor 4.35 (class ≤ 2 case) で結論.

下流: BG §1 Thm 1.11 (BG Cor 1.12 等), Ch.5 Cor 5.30 経由 normal p-complement (5.26). -/
theorem isaacs_thm_4_36 {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    (φ : A →* MulAut G) (hG : IsPGroup p G) (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ g : G, g ^ p = 1 → ∀ a : A, (φ a) g = g) :
    actionCommutator φ = ⊥ :=
  isaacs_thm_4_36_aux hp_odd hA_p' (Nat.card G) φ hG h_fix le_rfl

/-- **Isaacs Lemma 4.32 (後半)** ⭐: `P` p-群 が `G` 非自明 p-群 に作用 ⇒
`C_G(P)` (= fixed point subgroup) は非自明.

**proof**: `MulAction P G` を `φ` 経由で setup. `card_modEq_card_fixedPoints` で
`|G| ≡ |fixedPoints| mod p`. G 非自明 p-群より `p ∣ |G|`. 1 は trivial fixed point.
`exists_fixed_point_of_prime_dvd_card_of_fixed_point` で `1` と異なる fixed point 存在. -/
theorem fixedPoints_ne_bot_of_pgroup_action_pgroup
    {G P : Type*} [Group G] [Group P] [Finite G] [Finite P] [Nontrivial G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) (hP : IsPGroup p P)
    (φ : P →* MulAut G) :
    Subgroup.fixedPointsOfMulAut φ ≠ ⊥ := by
  letI : MulAction P G := MulAction.compHom G φ
  -- 1 ∈ fixedPoints (φ p is a group hom, so (φ p) 1 = 1)
  have h1_fix : (1 : G) ∈ MulAction.fixedPoints P G := fun p => by
    show (φ p) 1 = 1
    exact map_one (φ p)
  -- p ∣ |G| since G is a nontrivial p-group
  obtain ⟨n, hn_pos, hn_card⟩ := hG.nontrivial_iff_card.mp inferInstance
  have hp_dvd : p ∣ Nat.card G := by
    rw [hn_card]; exact dvd_pow_self p hn_pos.ne'
  -- ∃ b ∈ fixedPoints, b ≠ 1
  obtain ⟨b, hb_fix, hb_ne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := G) hp_dvd h1_fix
  -- b ∈ Subgroup.fixedPointsOfMulAut φ via the same definition
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨b, ?_⟩, ?_⟩
  · exact fun p => hb_fix p
  · intro h
    apply hb_ne
    exact (Subtype.ext_iff.mp h).symm

                                                                                   
                                                                   

                                                                                            
                                                                               
                                                      

                                                                                                

                                                                      
                                                  
                                                                          
                                                                    
                            
                                                          
                                                             
                                                                
                                            
                                                       
                                                                      
                                            
                                                 
                                                    
                                        
                                         
                                                        
         
          
                                                                            
                                            

/-- The left factor inclusion `P →* P × Q`. -/
def prodLeftHom (P Q : Type*) [Group P] [Group Q] : P →* P × Q where
  toFun p := (p, 1)
  map_one' := rfl
  map_mul' _ _ := by
    ext <;> simp

@[simp]
theorem prodLeftHom_apply {P Q : Type*} [Group P] [Group Q] (p : P) :
    prodLeftHom P Q p = (p, 1) :=
  by simp [prodLeftHom]

/-- The right factor inclusion `Q →* P × Q`. -/
def prodRightHom (P Q : Type*) [Group P] [Group Q] : Q →* P × Q where
  toFun q := (1, q)
  map_one' := rfl
  map_mul' _ _ := by
    ext <;> simp

@[simp]
theorem prodRightHom_apply {P Q : Type*} [Group P] [Group Q] (q : Q) :
    prodRightHom P Q q = (1, q) :=
  by simp [prodRightHom]

                                                                               
                   
                                                                          
                                                                               
                                                                                             
                                                                  
         
                                  
                                                    
                                                                                    
             
                       
           
                                                                          
                                                        
                                                                   
                                                         
                                                    
                                                  
                                         
                                                                  
       
                     
                                         
                                                                    
                          
                                                                           
            
                                                                                               
                                                             
                       
           
                                                    
                                                                                           
                                                        
                                                                   
                                                         
                                                    
                                                  
                                         
                                                                                         

                                                                          
                                                                           
                                                            
                                 
                                                                                     
                                                                  
         
                                  
                                      
                                                                  
             
                       
           
                                                                          
                                                                                
                                         
                                                                  
       
                     
                                         
                                           
                                                            
                                                                 
                          
                                                             
            
                                              
                                                                             
                                                                             
                                                                         
                       
           
                                                    
                                                                                           
                                                                                
                                         
                                                                                         

                                        

                                                                         
                                                                      
                                                                         
                                                               
                                                                            
                                                                                   
                                                                                        
                                                    
                                                
                                                         
                                                                     
           
                                  
                                                                                
                                                                               
                    
                                                     
                              
                                                                       
                                                 
                                                       
                                      
                           
                                                                                 
                                                                                       
                                                   
                                                        
                                                                        
                     
                                                               
                                                       
                                      
                                                               
           
                                                                                  
                               
                                                            
                          
                                                                                           
                                                     
                                    
                                                 
                   
             
                   
                   
                 

                                                                                 

                                                                           
                                                                         
                                                                               
                                                                                              
                                                                             
                                                                                  
                          
                                                                       
                             
                                           
                                            
                                           
                                                             
                                           
                                                                            
                                           
                                                                            
                                                    
                                                                              
                                                                
                                                    
                                                                              
                                                                
                                                  
                                                        
                                            
                                                             
                                                                               
                                                               
                                        
                                      
                                                                                  
                            
                   
                                      
                                           
                                        
                                                                  
                                                                               
                         
                                                
                                                  
             
                                         
                                                
                                                                 
                                                  
                                                   
              
                                                                                      
                    
                          
                                                                      
                                                                   
                                                           
                                                                      
                                                                                     
                   
                    
                                                                           
                                            
                                                               
                                                                                         
                              
                             

                                                                                      

                                                                         
                                                                           
                                                                        
                                
                                                                                      
                                                                       
                                                             
                                                     
                                                                                  
                        
                                                                                          
                                                             
                                                         
                 
                                                                         
                            
                                                                                          
                 
                                                                              
                
                                                    
             
                                                  
                                      
                                                         
                                                                     
           
                                                                               
                                               
                                                                                
                                                                    
                                                   

                                                                 
                                                                   
                                       
                                 
                                           
                                                     
                                                                           
                                                     
                                         
                                    

                                                                                 
                                            
                                                           
                                                                                     
                                                     
                                                  
                                                                                     
                                                                                  
         
                  
           
                          
           
                                               
         
                
                                
                                                             
                                                    
                                                               
                                      
        
                                                                              
                                                     
               
                                 
                                     
                                                          
                                                          
                                                                            
                                                                
                                                                
                                                          
                                    
                
                                                                       
                                                                   
                 
                                             
                                                   
                             
                                                                                     
                                                              
                 
                                                                                      
                                     
                                                          
                                                   
                  
                                                                                          
                      
                       
                                                                  
               
                                                               
                            
                                             
                              
                                        
                                                    
                   
                                                                                                  
                  
                                                              
                                 
                               
                                                                              
                            
                                                                                        
                                

                                                           

                                                                     
                                                                           
                                                         
                                
                                                                                  
                                                        
                                                                         
                                                                                          
                                                          
                                                                       

                                                                                
                                          

                                                                             
                                                                              
                                                                             
                                                                               
                                                                         
                                 
                                                      
                                                             
                                          
                                                             
                                              
                                                     
                                                                          
           
                                                                   
                                                                   
                                                    
                       
                                                                          
                                                             
                              
               
                                
                                    
                        
                                       
                                  
               
                  
                                  
               
                  
                                  
                
                                                                 
              
                                                                                 
               
                                                                            
                                        
                
                                                   
                                                                       
                                 
                                                                        
                                                              
                                 
                                
                            
                  
               
         
                              
                                                                    
                                                             
                                                      
                                                                   
                                                                      
             
                                                 
                                                                                 
                                
               
                                                  
             
                                                                                       
                
                                                                     
                                       
                 
                      
                                         
                                                                                           
                                                        
                                                                     
          
                                                            
                                         
                                  
                 
                                                        
                              
                                                      
                                      
                  
                                                           
                                
                                            
                     
                                  
                                 
                                   
                     
                         
                         
                                                    
                                
                  
                          
                      
                                                                          
                                                                
                                        
                                          
                     
                                                                  
                                                                   
          
                                                                                            
                          
                                                               
                                                                 
                                                                        
                                                     
                                                            
                           
                                   
             
                           
                            
                                                                 
                                                                
                                                              
                                                        
        
                         
                                                                              
                                             
                

                                                                            
                                                                       
                                   

                                                             
                                                                               
                                                                        
                                                               
                                                             
                                                          
                                                                             
                                          
                                                            
                                                     
           
                                                                   
                                                                   
                       
                                                                          
                                                   
                
                                                                
                                       
                                                             
                                                                
               
                                 
                                                       
                                
               
                                                  
                                                
                                                                           
                                        
              
                                                                                 
               
                                                                            
               
                                                                                 
              
                                              
                 
                          
                                                                                   
                    
                    
                                                      
                                                                    
                                                    
                          
                                                                
                                                                       
                                    

                                                            

                                                                
                                                                                 
    

                                                                          
                                                                            
                                                                               
                                 
                                                  
                                                             
                                                          
                                                               
                                                                                  
                                                                      
           
                                                                
                                                                      
                                                           
                                                         
                                                                      
                              
                                                                   
               
                                                    
                                               
                
                                                   
                                                                       
                                             
                           
                          
                                                                
                          
                                                                             
                                                                              
                                                                                       
                                                                         
                                                                   
                 
                                                                 
                                                         
                                         
                                                                      
                                  
               
                  
                                                                     
                                                                   
               
                                                    
                                                                               
              
                                                                                  
                                                                       
                                                                
                                       
                                   
                                
                           
                                                        
                                               
                                    
                                                  
                                                          
       
                      
                                   
                              

                                                    
                                   
                                    
                                                    
                                                                                     
                                                     
                                             
                                                                                   
                                                                         
         
                  
           
                          
           
                                               
         
                
                                
                                                             
                                                    
                                      
        
                                                                              
                                                     
               
                                 
                                     
                                                  
                                                           
                                                                       
             
                                                                                 
                                                         
                                                            
                                                                
                                                  
        
                                                             
                                                                                      
                                                                
                   
                                                                                           
                                  
                                                            
                                                     
                    
                                                                                          
                        
                         
                                                                   
                 
                                                                 
                              
                                               
                                
                                          
                                                      
                                                                  
                    
                                                                
                                                                            
                              
                                                                        
                                                       
                                                    
                                                             
                                                          
                                                                               
                                                   
                                               
                                  
                                                           
                                                      
                   
                                                                                                
                       
                       
                                                                   
               
                                                                
                             
                                              
                               
                                            
                                                      
                                                                       
                    
                                                               
                                                                              
                             
                                                                
                                                                                             
                                                                                             
                                                                                               
                                              
                                               
                                                
                                                                   
                                         
                                            
                                                                          
                                 
                       
                                                 
                                   
                                                
                                                                                           
                                                                    
                                                                 
                                        
                                                    
                                                                        
                                                   
                                  
                                    
                                                    
                       
                                                                                                  
                            
                                                    
                    
                                             
                                                     
                                                               
                                                 
                                                       
                                             
                                                 
                                     
                          
                                                                         
                                                                  
                                                                                         
                                         
                                                                                  
                          
                                                                        
                
                                  
             
                                               
                            
                                                      
                                                                     
                                           
             
                      
                                                      
                                                                                  
                                                                               
                                                                            
                     
                                                             
                                            
                      
                                                                                 
               
                                                   
                             
                                                                  
                                        
                                                         
                  
                             
                      
                                                                       
                                           
                                                                 
                                                   
             
                                              
                                                                
                                                                                
                                                                       
                                    
                            
                   
                 
                                    

                            

                                                                       
                                                                        
                         
                       
                                                           
                                               
                                              
                                                                                   
                                                                                        
                                                 
                                                                         

end -- 4D

end OddOrder.Isaacs.Ch04
