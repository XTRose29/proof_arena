import Mathlib
import ChallengeDeps

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Arithmetic.lean
section
open scoped BigOperators
open Polynomial
open Finset

noncomputable section

lemma coeff_finpoly (a : ℕ → ℝ) {N : ℕ} (hN : ∀ n ≥ N, a n = 0) :
  ∀ n, (∑ i ∈ Finset.range N, Polynomial.monomial i (a i) : ℝ[X]).coeff n = a n := by
  intro n
  classical
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  -- want sum ite
  classical
  rw [Finset.sum_ite_eq' (Finset.range N) n a]
  by_cases hn : n < N
  · simp [Finset.mem_range.2 hn]
  · have hn' : N ≤ n := Nat.le_of_not_gt hn
    simp [Finset.mem_range, hn, hN n hn']

lemma coeff_X_sq_mul_zero {A : ℝ[X]} : (Polynomial.X ^ 2 * A).coeff 0 = 0 := by
  simpa using (Polynomial.coeff_X_pow_mul' A 2 0)
lemma coeff_X_sq_mul_one {A : ℝ[X]} : (Polynomial.X ^ 2 * A).coeff 1 = 0 := by
  simpa using (Polynomial.coeff_X_pow_mul' A 2 1)

lemma qp_expand (d r : ℝ) (A : ℝ[X]) :
    (1 - Polynomial.C d * Polynomial.X + Polynomial.C r * Polynomial.X ^ 2) * A =
      A - Polynomial.C d * (Polynomial.X * A) + Polynomial.C r * (Polynomial.X ^ 2 * A) := by
  ring

lemma qA_coeff_zero (a : ℕ → ℝ) {N : ℕ} (hN : ∀ n ≥ N, a n = 0)
    (d r : ℝ) :
 let A : ℝ[X] := ∑ i ∈ Finset.range N, Polynomial.monomial i (a i)
 ((1 - Polynomial.C d * Polynomial.X + Polynomial.C r * Polynomial.X ^ 2) * A).coeff 0 = a 0 := by
  dsimp
  rw [qp_expand]
  simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul_zero, coeff_X_sq_mul_zero, coeff_finpoly a hN]

lemma qA_coeff_one (a : ℕ → ℝ) {N : ℕ} (hN : ∀ n ≥ N, a n = 0)
    (d r : ℝ) :
 let A : ℝ[X] := ∑ i ∈ Finset.range N, Polynomial.monomial i (a i)
 ((1 - Polynomial.C d * Polynomial.X + Polynomial.C r * Polynomial.X ^ 2) * A).coeff 1 = a 1 - d * a 0 := by
  dsimp
  rw [qp_expand]
  -- simp maybe
  simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul, coeff_X_sq_mul_one, coeff_finpoly a hN]

lemma qA_coeff_two_add (a : ℕ → ℝ) {N : ℕ} (hN : ∀ n ≥ N, a n = 0)
    (d r : ℝ) (n : ℕ) :
 let A : ℝ[X] := ∑ i ∈ Finset.range N, Polynomial.monomial i (a i)
 ((1 - Polynomial.C d * Polynomial.X + Polynomial.C r * Polynomial.X ^ 2) * A).coeff (n+2) =
    a (n+2) - d * a (n+1) + r * a n := by
  dsimp
  rw [qp_expand]
  simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_mul,
    coeff_finpoly a hN]
  -- ?

lemma one_le_eval_of_coeff_nonneg (P : ℝ[X]) (hP : ∀ n, 0 ≤ P.coeff n)
    (h0 : P.coeff 0 = 1) {t : ℝ} (ht : 0 ≤ t) : 1 ≤ P.eval t := by
  rw [Polynomial.eval_eq_sum_range]
  -- apply single_le_sum
  have hmem : 0 ∈ Finset.range (P.natDegree + 1) := by exact Finset.mem_range.mpr (Nat.zero_lt_succ _)
  have hnon : ∀ i ∈ Finset.range (P.natDegree + 1), 0 ≤ P.coeff i * t ^ i := by
    intro i hi
    exact mul_nonneg (hP i) (pow_nonneg ht i)
  have hle := Finset.single_le_sum hnon hmem
  -- hle : coeff0 * t^0 ≤ sum
  simpa [h0] using hle

theorem numerical_gs (d r : ℝ) (hd : 0 < d)
 (a : ℕ → ℝ) (ha0 : a 0 = 1) (ha : ∀ n, 0 ≤ a n)
 (hev : ∃ N, ∀ n ≥ N, a n = 0)
 (hb1 : 0 ≤ a 1 - d * a 0)
 (hb : ∀ n, 0 ≤ a (n+2) - d * a (n+1) + r * a n) :
 d^2 < 4 * r := by
  by_contra! hbad
  obtain ⟨N, hN⟩ := hev
  let A : ℝ[X] := ∑ i ∈ Finset.range N, Polynomial.monomial i (a i)
  let q : ℝ[X] := 1 - Polynomial.C d * Polynomial.X + Polynomial.C r * Polynomial.X ^ 2
  let P : ℝ[X] := q * A
  have hAcoeff (n : ℕ) : A.coeff n = a n := by
    dsimp [A]
    exact coeff_finpoly a hN n
  have hP0 : P.coeff 0 = 1 := by
    dsimp [P, q, A]
    rw [qA_coeff_zero a hN d r]
    exact ha0
  have hPn : ∀ n : ℕ, 0 ≤ P.coeff n := by
    intro n
    rcases n with (_ | n)
    · rw [hP0]
      exact zero_le_one
    · rcases n with (_ | n)
      · -- n=1
        dsimp [P, q, A]
        rw [qA_coeff_one a hN d r]
        exact hb1
      · -- n+2
        dsimp [P, q, A]
        rw [qA_coeff_two_add a hN d r n]
        exact hb n
  let t : ℝ := 2 / d
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hPeval : 1 ≤ P.eval t := one_le_eval_of_coeff_nonneg P hPn hP0 ht
  have hAeval : 0 ≤ A.eval t := by
    have hacoeff : ∀ n : ℕ, 0 ≤ A.coeff n := by intro n; rw [hAcoeff]; exact ha n
    have h := one_le_eval_of_coeff_nonneg A hacoeff (by rw [hAcoeff, ha0]) ht
    linarith
  have hqeval : q.eval t = 1 - d * t + r * t^2 := by
    dsimp [q]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
  have hqt : q.eval t ≤ 0 := by
    rw [hqeval]
    dsimp [t]
    have hd0 : d ≠ 0 := ne_of_gt hd
    field_simp
    nlinarith
  have hPE : P.eval t = q.eval t * A.eval t := by
    dsimp [P]
    rw [Polynomial.eval_mul]
  have : P.eval t ≤ 0 := by rw [hPE]; exact mul_nonpos_of_nonpos_of_nonneg hqt hAeval
  linarith

/-- A convenient natural-number version of the coefficient inequality.  Dimensions
of layers of a filtered finite algebra are naturals; phrasing the recurrence with
addition avoids the truncated subtraction on `ℕ`. -/
theorem numerical_gs_nat (d r : ℕ) (hd : 0 < d)
    (a : ℕ → ℕ) (ha0 : a 0 = 1)
    (hfin : ∃ N : ℕ, ∀ n ≥ N, a n = 0)
    (h1 : d * a 0 ≤ a 1)
    (hstep : ∀ n : ℕ, d * a (n+1) ≤ a (n+2) + r * a n) :
    (d : ℝ)^2 < 4 * (r : ℝ) := by
  let a' : ℕ → ℝ := fun n => (a n : ℝ)
  have hd' : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have ha0' : a' 0 = 1 := by simpa [a'] using congrArg (fun n : ℕ => (n:ℝ)) ha0
  have ha' : ∀ n : ℕ, 0 ≤ a' n := by
    intro n
    dsimp [a']
    exact_mod_cast (Nat.zero_le (a n))
  have hfin' : ∃ N : ℕ, ∀ n ≥ N, a' n = 0 := by
    obtain ⟨N,hN⟩ := hfin
    refine ⟨N, ?_⟩
    intro n hn
    simp [a', hN n hn]
  have h1' : 0 ≤ a' 1 - (d:ℝ) * a' 0 := by
    have hz : (d:ℝ) * a' 0 ≤ a' 1 := by
      dsimp [a']
      exact_mod_cast h1
    linarith
  have hstep' : ∀ n : ℕ,
      0 ≤ a' (n+2) - (d:ℝ) * a' (n+1) + (r:ℝ) * a' n := by
    intro n
    have hn : (d:ℝ) * a' (n+1) ≤ a' (n+2) + (r:ℝ) * a' n := by
      dsimp [a']
      exact_mod_cast (hstep n)
    linarith
  exact numerical_gs (d : ℝ) (r : ℝ) hd' a' ha0' ha' hfin' h1' hstep'

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Arithmetic.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Generator.lean
section
namespace GSsupport
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]
lemma tclose_eq (H : Subgroup G) : H.topologicalClosure = H := by
  ext x
  change x ∈ closure (H:Set G) ↔ x ∈ (H:Set G)
  rw [IsClosed.closure_eq (isClosed_discrete _)]
lemma zero_gen_not_top [Nontrivial G] :
 ¬ ∃ S : Finset G, S.card = 0 ∧ (Subgroup.closure (S : Set G)).topologicalClosure = ⊤ := by
  rintro ⟨S, hS, htop⟩
  have hEmpty : S = ∅ := Finset.card_eq_zero.mp hS
  subst S
  have hbot : (Subgroup.closure ((∅ : Finset G) : Set G)).topologicalClosure = (⊥ : Subgroup G) := by
    rw [show ((∅ : Finset G) : Set G) = (∅ : Set G) by ext; simp,
       Subgroup.closure_empty, tclose_eq]
  rw [hbot] at htop
  have hall : ∀ g : G, g = 1 := by
    intro g
    have ht : g ∈ (⊤ : Subgroup G) := trivial
    have hb : g ∈ (⊥ : Subgroup G) := by simpa [htop] using ht --?
    simpa using hb
  have hsub : Subsingleton G := ⟨by
    intro a b
    calc
      a = 1 := hall a
      _ = b := (hall b).symm ⟩
  exact not_subsingleton G hsub

lemma my_generator_rank_pos [Nontrivial G] [Finite G] :
  0 < sInf {k : ℕ | ∃ S : Finset G, S.card = k ∧ (Subgroup.closure (S : Set G)).topologicalClosure = ⊤} := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let T : Set ℕ := {k : ℕ | ∃ S : Finset G, S.card = k ∧ (Subgroup.closure (S : Set G)).topologicalClosure = ⊤}
  have hT : T.Nonempty := by
    refine ⟨Finset.card (Finset.univ : Finset G), ?_⟩
    refine ⟨(Finset.univ : Finset G), rfl, ?_⟩
    have hu : (((Finset.univ : Finset G) : Set G)) = (Set.univ : Set G) := by ext; simp
    rw [hu, Subgroup.closure_univ]
    exact tclose_eq G _
  have hz : (0:ℕ) ∉ T := by
    intro hz
    exact zero_gen_not_top G hz
  change 0 < sInf T
  have hnz : sInf T ≠ 0 := by
    intro h
    rcases (Nat.sInf_eq_zero.mp h) with h0 | hempty
    · exact hz h0
    · exact hT.ne_empty hempty
  exact Nat.pos_of_ne_zero hnz
end GSsupport

namespace GSsupport
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DiscreteTopology G]

/-- In the discrete topology the extra closure in the definition of the generator
rank is harmless.  It is useful to eliminate it before doing finite group algebra. -/
lemma closure_finset_tclose (S : Finset G) :
    (Subgroup.closure (S : Set G)).topologicalClosure = Subgroup.closure (S : Set G) :=
  tclose_eq G _

lemma inf_generators_is_attained [Finite G] :
  let T : Set ℕ := {k : ℕ | ∃ S : Finset G, S.card = k ∧
      (Subgroup.closure (S : Set G)).topologicalClosure = ⊤}
  ∃ S : Finset G, S.card = sInf T ∧ Subgroup.closure (S : Set G) = ⊤ := by
  classical
  dsimp
  -- first, this set isn't empty (use all group elements)
  have hT : ({k : ℕ | ∃ S : Finset G, S.card = k ∧
      (Subgroup.closure (S : Set G)).topologicalClosure = ⊤} : Set ℕ).Nonempty := by
    letI : Fintype G := Fintype.ofFinite G
    refine ⟨Finset.card (Finset.univ : Finset G), ?_⟩
    refine ⟨(Finset.univ : Finset G), rfl, ?_⟩
    have hu : (((Finset.univ : Finset G) : Set G)) = (Set.univ : Set G) := by ext; simp
    rw [hu, Subgroup.closure_univ]
    exact tclose_eq G _
  have hm := Nat.sInf_mem hT
  rcases hm with ⟨S, hcard, hgen⟩
  refine ⟨S, hcard, ?_⟩
  rw [closure_finset_tclose G S] at hgen
  exact hgen

lemma inf_generators_le_card [Finite G] :
  sInf {k : ℕ | ∃ S : Finset G, S.card = k ∧
      (Subgroup.closure (S : Set G)).topologicalClosure = ⊤} ≤ Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hm : (Finset.univ : Finset G).card = Nat.card G := by simp
  refine hm ▸ Nat.sInf_le ?_
  refine ⟨(Finset.univ : Finset G), rfl, ?_⟩
  rw [closure_finset_tclose G]
  have hu : (((Finset.univ : Finset G) : Set G)) = (Set.univ : Set G) := by ext; simp
  rw [hu, Subgroup.closure_univ]
end GSsupport

namespace GSsupport
variable (G:Type*) [Group G]

/-- The free group on a finite generating set, mapped to its elements.  This is
 the presentation map from which the pro-p presentation in GS starts. -/
noncomputable def genLift (S : Finset G) :
    FreeGroup {x : G // x ∈ S} →* G :=
  FreeGroup.lift (fun x : {x : G // x ∈ S} => x.1)
lemma genLift_range (S : Finset G) :
    (genLift G S).range = Subgroup.closure (S : Set G) := by
  rw [genLift, FreeGroup.range_lift_eq_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
lemma genLift_surj {S : Finset G} (h : Subgroup.closure (S:Set G) = ⊤) :
    Function.Surjective (genLift G S) := by
  apply MonoidHom.range_eq_top.mp
  rw [genLift_range G S, h]
end GSsupport

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Generator.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Reduction.lean
section
noncomputable section
open scoped BigOperators

namespace GSsupport
noncomputable def eps (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q] :
    MonoidAlgebra (ZMod p) Q →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (ZMod p) Q (1 : Q →* ZMod p)
noncomputable def aug (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q] :
    Submodule (ZMod p) (MonoidAlgebra (ZMod p) Q) :=
  LinearMap.ker (eps p Q).toLinearMap
abbrev augLayer (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
  (n : ℕ) : Type _ :=
    ↥(aug p Q ^ n) ⧸
      (aug p Q ^ (n+1)).comap (aug p Q ^ n).subtype
noncomputable def augCoeffs (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
    (n : ℕ) : ℕ := Module.finrank (ZMod p) (augLayer p Q n)
end GSsupport
namespace GSsupport
lemma aug_comap_one_bot (p:ℕ) [Fact p.Prime] (Q:Type*) [Group Q] :
   (aug p Q).comap ((1 : Submodule (ZMod p) (MonoidAlgebra (ZMod p) Q)).subtype) = ⊥ := by
  -- kernel has no scalars
  ext x
  constructor
  · intro hx
    change (eps p Q) ((↑x) : MonoidAlgebra (ZMod p) Q) = 0 at hx
    have hxran : (x : MonoidAlgebra (ZMod p) Q) ∈
        LinearMap.range (Algebra.linearMap (ZMod p) (MonoidAlgebra (ZMod p) Q)) := by
      simpa [Submodule.one_eq_range] using x.property
    obtain ⟨r, hr⟩ := hxran
    change algebraMap (ZMod p) (MonoidAlgebra (ZMod p) Q) r = (x : MonoidAlgebra (ZMod p) Q) at hr
    have hr0 : r = 0 := by
      have : r = (eps p Q) (algebraMap (ZMod p) (MonoidAlgebra (ZMod p) Q) r) := by
        simpa using ((eps p Q).commutes r).symm
      rw [hr, hx] at this
      simpa using this
    have xx : (x : MonoidAlgebra (ZMod p) Q) = 0 := by
      calc
        (x : MonoidAlgebra (ZMod p) Q) = algebraMap (ZMod p) (MonoidAlgebra (ZMod p) Q) r := hr.symm
        _ = 0 := by simpa only [hr0, map_zero]
    change x = 0
    exact Subtype.ext xx
  · intro hx
    change (eps p Q) ((↑x) : MonoidAlgebra (ZMod p) Q) = 0
    have : x = 0 := by simpa using hx
    subst x
    simp
end GSsupport
--#reduce GSsupport.eps

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Reduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Nilpotence.lean
section
noncomputable section
open scoped BigOperators
namespace GSsupport
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- stable for left multiplication by a group basis vector -/
def LeftInv (W : Submodule k B) : Prop :=
  ∀ (q : Q) (x : B), x ∈ W → (MonoidAlgebra.of k Q q) * x ∈ W

lemma aug_leftInv : LeftInv p Q (aug p Q) := by
 intro q x hx
 change (eps p Q) ((MonoidAlgebra.of k Q q) * x) = 0
 change (eps p Q) x = 0 at hx
 rw [map_mul, hx, mul_zero]

lemma pow_leftInv (n : ℕ) : LeftInv p Q (aug p Q ^ (n+1)) := by
 induction n with
 | zero => simpa using (aug_leftInv p Q)
 | succ n ih =>
   rw [pow_succ']
   intro q x hx
   refine Submodule.mul_induction_on hx ?_ ?_
   · intro a ha b hb
     -- a is in aug, b in power previous? because pow_succ' expansion for n+2 = aug * aug^(n+1)
     rw [← mul_assoc]
     apply Submodule.mul_mem_mul ?_ hb
     -- need aug left stable
     exact aug_leftInv p Q q a ha
   · intro x y hx hy
     simpa [mul_add] using (aug p Q * aug p Q ^ (n+1)).add_mem hx hy

/-- left action restricted to a stable subspace -/
def actLin (W : Submodule k B) (hW : LeftInv p Q W) (q : Q) :
    W →ₗ[k] W :=
 LinearMap.restrict ((Algebra.lmul k B) (MonoidAlgebra.of k Q q))
   (by
     intro x hx
     exact hW q x hx)

@[simp] lemma actLin_val (W : Submodule k B) (hW : LeftInv p Q W) (q : Q) (x : W) :
 ((actLin p Q W hW q x : W) : B) = (MonoidAlgebra.of k Q q) * (x : B) := rfl

/-- the underlying group action on a stable subspace -/
def invAction (W : Submodule k B) (hW : LeftInv p Q W) : MulAction Q W where
 smul q x := actLin p Q W hW q x
 one_smul x := by
   apply Subtype.ext
   change (MonoidAlgebra.of k Q (1:Q)) * (x:B) = (x:B)
   rw [map_one, one_mul]
 mul_smul q r x := by
   apply Subtype.ext
   change (MonoidAlgebra.of k Q (q*r)) * (x:B) = _
   change _ = (MonoidAlgebra.of k Q q) * ((MonoidAlgebra.of k Q r) * (x:B))
   rw [← mul_assoc, map_mul]

/-- contragredient action on the dual of a stable subspace -/
def dualAction (W : Submodule k B) (hW : LeftInv p Q W) :
    MulAction Q (Module.Dual k W) where
 smul q f := f.comp (actLin p Q W hW q⁻¹)
 one_smul f := by
   apply LinearMap.ext
   intro x
   change f (actLin p Q W hW (1:Q)⁻¹ x) = f x
   congr 1
   apply Subtype.ext
   change (MonoidAlgebra.of k Q ((1:Q)⁻¹)) * (x:B) = (x:B)
   rw [inv_one, map_one, one_mul]
 mul_smul q r f := by
   apply LinearMap.ext
   intro x
   change f (actLin p Q W hW (q*r)⁻¹ x) =
      f (actLin p Q W hW r⁻¹ (actLin p Q W hW q⁻¹ x))
   congr 1
   apply Subtype.ext
   change (MonoidAlgebra.of k Q ((q*r)⁻¹)) * (x:B) =
      (MonoidAlgebra.of k Q r⁻¹) * ((MonoidAlgebra.of k Q q⁻¹) * (x:B))
   rw [mul_inv_rev, map_mul, mul_assoc]

/-- a nonzero stable subspace has a nonzero invariant linear functional (the
    elementary fixed point lemma for a representation of a finite p-group). -/
lemma exists_invariant_functional [Finite Q] (hp : IsPGroup p Q)
    (W : Submodule k B) (hW : LeftInv p Q W) (hne : W ≠ ⊥) :
    ∃ f : Module.Dual k W, f ≠ 0 ∧
      ∀ (q : Q) (x : W), f (actLin p Q W hW q x) = f x := by
 classical
 -- install the finite incarnations of the group algebra (finsupp's `fintype` is a definition)
 letI : Fintype Q := Fintype.ofFinite Q
 letI : DecidableEq Q := Classical.decEq Q
 letI : Fintype B := Finsupp.fintype
 letI : Fintype W := Fintype.ofFinite W
 letI : Finite (Module.Dual k W) := DFunLike.finite (Module.Dual k W)
 letI : Fintype (Module.Dual k W) := Fintype.ofFinite _
 letI : MulAction Q (Module.Dual k W) := dualAction p Q W hW
 have hdim : 0 < Module.finrank k W := (Nat.pos_iff_ne_zero).2 (by
   intro h
   exact hne (Submodule.finrank_eq_zero.mp h))
 have hcard : p ∣ Nat.card (Module.Dual k W) := by
   rw [Nat.card_eq_fintype_card,
       @Module.card_eq_pow_finrank k (Module.Dual k W),
       @Subspace.dual_finrank_eq k W, ZMod.card]
   exact dvd_pow_self p (Nat.ne_of_gt hdim)
 have hzero : (0 : Module.Dual k W) ∈ MulAction.fixedPoints Q (Module.Dual k W) := by
   rw [MulAction.mem_fixedPoints]
   intro q
   apply LinearMap.ext
   intro x
   change (0 : Module.Dual k W).comp _ x = (0 : Module.Dual k W) x
   rfl
 obtain ⟨f, hf, hfne⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (Module.Dual k W) hcard hzero
 refine ⟨f, ?_, ?_⟩
 · intro h
   have : (0 : Module.Dual k W) = f := by simpa [h] using (rfl : (0 : Module.Dual k W) = 0)
   exact hfne this
 · intro q x
   have hfix : ∀ g : Q, g • f = f := (MulAction.mem_fixedPoints.mp hf)
   have hs := congrArg (fun (l : Module.Dual k W) => l x) (hfix q⁻¹)
   -- action by inverse is precomposition by q
   change f (actLin p Q W hW (q⁻¹)⁻¹ x) = f x at hs
   simpa using hs

/-- stability under the group basis implies stability under all of the group algebra. -/
lemma all_left (W : Submodule k B) (hW : LeftInv p Q W)
    (a : B) (x : B) (hx : x ∈ W) : a * x ∈ W := by
 induction a using MonoidAlgebra.induction_on with
 | hM q => exact hW q x hx
 | hadd a b ha hb => simpa [add_mul] using W.add_mem ha hb
 | hsmul r a ha =>
   simpa [smul_mul_assoc] using W.smul_mem r ha

/-- an invariant functional is augmentation on a column: `f(a x)=ε(a) f(x)`. -/
lemma invariant_eval (W : Submodule k B) (hW : LeftInv p Q W)
    (f : Module.Dual k W)
    (hf : ∀ (q : Q) (x : W), f (actLin p Q W hW q x) = f x)
    (a : B) (x : W) :
    f ⟨a * (x:B), all_left p Q W hW a x x.property⟩ = (eps p Q a) * f x := by
 induction a using MonoidAlgebra.induction_on with
 | hM q =>
   -- this is precisely invariance under a basis element
   change f (actLin p Q W hW q x) = _
   simpa [eps, mul_comm] using hf q x
 | hadd a b ha hb =>
   -- proof fields of the subtype disappear by extensionality
   have hsum :
     (⟨(a+b) * (x:B), all_left p Q W hW (a+b) x x.property⟩ : W) =
       ⟨a * (x:B), all_left p Q W hW a x x.property⟩ +
       ⟨b * (x:B), all_left p Q W hW b x x.property⟩ := by
       apply Subtype.ext
       simp [add_mul]
   rw [hsum, map_add, ha, hb, map_add, add_mul]
 | hsmul r a ha =>
   have hsc :
     (⟨(r • a) * (x:B), all_left p Q W hW (r • a) x x.property⟩ : W) =
       r • (⟨a * (x:B), all_left p Q W hW a x x.property⟩ : W) := by
       apply Subtype.ext
       simp [smul_mul_assoc]
   rw [hsc, map_smul, ha, map_smul]
   -- scalar associativity in the coefficient field
   simp [smul_eq_mul, mul_assoc]

/-- Each nonzero augmentation power drops at the next step (Nakayama/fixed point argument). -/
lemma aug_power_strict [Finite Q] (hp : IsPGroup p Q) (n : ℕ)
    (hne : aug p Q ^ (n+1) ≠ ⊥) :
    aug p Q ^ (n+2) ≠ aug p Q ^ (n+1) := by
  classical
  let W : Submodule k B := aug p Q ^ (n+1)
  have hW : LeftInv p Q W := pow_leftInv p Q n
  obtain ⟨f, hf0, hf⟩ := exists_invariant_functional p Q hp W hW (by simpa [W] using hne)
  -- multiplication by anything preserves W
  have hmul : aug p Q * W ≤ W := by
    refine Submodule.mul_le.mpr ?_
    intro a ha b hb
    exact all_left p Q W hW a b hb
  intro heq
  have heq' : aug p Q * W = W := by
    simpa [W, pow_succ'] using heq
  -- f annihilates every element of J*W
  have hann : ∀ y : B, (hy : y ∈ aug p Q * W) →
      f (⟨y, hmul hy⟩ : W) = 0 := by
    intro z hz
    refine Submodule.mul_induction_on' (M:=aug p Q) (N:=W)
      (C:= fun y hy => f (⟨y, hmul hy⟩ : W) = 0) ?_ ?_ hz
    · intro a ha b hb
      have ha0 : eps p Q a = 0 := ha
      have hv := invariant_eval p Q W hW f hf a (⟨b, hb⟩ : W)
      simpa [ha0] using hv
    · intro x hx y hy hx0 hy0
      have hxy : (⟨x+y, hmul ((aug p Q * W).add_mem hx hy)⟩ : W) =
             (⟨x, hmul hx⟩ : W) + (⟨y, hmul hy⟩ : W) := by
             rfl
      rw [hxy, map_add, hx0, hy0, add_zero]
  -- if J W = W that says f is zero on all vectors
  have fzero : f = 0 := by
    apply LinearMap.ext
    intro x
    have hx' : (x:B) ∈ aug p Q * W := by
      rw [heq']
      exact x.property
    simpa using hann (x:B) hx'
  exact hf0 fzero

/-- some power of the augmentation submodule is zero for a finite p-group. -/
lemma aug_nilpotent [Finite Q] (hp : IsPGroup p Q) :
    ∃ N : ℕ, aug p Q ^ N = ⊥ := by
  classical
  -- choose a power `>=1` of smallest dimension
  let vals : Set ℕ := {d | ∃ n : ℕ, d = Module.finrank k (↥(aug p Q ^ (n+1)))}
  have hvals : vals.Nonempty := ⟨Module.finrank k (↥(aug p Q ^ (0+1))), 0, rfl⟩
  have hmin : sInf vals ∈ vals := csInf_mem hvals
  obtain ⟨n, hn⟩ := hmin
  have hle : ∀ m : ℕ, Module.finrank k (↥(aug p Q ^ (n+1))) ≤
        Module.finrank k (↥(aug p Q ^ (m+1))) := by
    intro m
    have hm : Module.finrank k (↥(aug p Q ^ (m+1))) ∈ vals := ⟨m, rfl⟩
    have := Nat.sInf_le hm
    -- hn identifies the minimum
    simpa [hn] using this
  let W : Submodule k B := aug p Q ^ (n+1)
  have hsub : aug p Q * W ≤ W := by
    refine Submodule.mul_le.mpr ?_
    intro a ha b hb
    exact all_left p Q W (pow_leftInv p Q n) a b hb
  have hsub' : aug p Q ^ (n+2) ≤ aug p Q ^ (n+1) := by
    simpa [W, pow_succ'] using hsub
  have heqr : Module.finrank k (↥(aug p Q ^ (n+2))) =
      Module.finrank k (↥(aug p Q ^ (n+1))) := by
    apply Nat.le_antisymm
    · exact Submodule.finrank_mono hsub'
    · simpa [Nat.add_assoc] using hle (n+1)
  have heq : aug p Q ^ (n+2) = aug p Q ^ (n+1) :=
    Submodule.eq_of_le_of_finrank_eq hsub' heqr
  have hz : aug p Q ^ (n+1) = (⊥ : Submodule k B) := by
    by_contra hne
    exact aug_power_strict p Q hp n hne heq
  exact ⟨n+1, hz⟩

lemma aug_zero_above [Finite Q] (hp : IsPGroup p Q) :
    ∃ N : ℕ, ∀ n ≥ N, augCoeffs p Q n = 0 := by
  classical
  obtain ⟨N, hN⟩ := aug_nilpotent p Q hp
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hpow : aug p Q ^ (N + m) = (⊥ : Submodule k B) := by
    rw [pow_add, hN, Submodule.bot_mul]
  unfold augCoeffs augLayer
  -- the numerator is the zero subspace hence the quotient is a singleton
  let T : Submodule k (↥(aug p Q ^ (N+m))) :=
       (aug p Q ^ (N+m+1)).comap (aug p Q ^ (N+m)).subtype
  have hsing : Subsingleton (↥(aug p Q ^ (N+m))) := by
    rw [hpow]
    infer_instance
  haveI : Subsingleton (↥(aug p Q ^ (N+m))) := hsing
  haveI hquot : Subsingleton ( (↥(aug p Q ^ (N+m))) ⧸
       ((aug p Q ^ (N+m+1)).comap (aug p Q ^ (N+m)).subtype)) :=
    (Submodule.Quotient.mk_surjective
       ((aug p Q ^ (N+m+1)).comap (aug p Q ^ (N+m)).subtype)).subsingleton
  exact Module.finrank_zero_of_subsingleton
lemma augCoeffs_zero (p:ℕ) [Fact p.Prime] (Q:Type*) [Group Q] :
    augCoeffs p Q 0 = 1 := by
  unfold augCoeffs augLayer
  -- simplify the first two powers
  rw [pow_zero (aug p Q), pow_one (aug p Q)]
  change Module.finrank (ZMod p)
    ((↥(1 : Submodule (ZMod p) (MonoidAlgebra (ZMod p) Q))) ⧸
      ((aug p Q).comap
        (1 : Submodule (ZMod p) (MonoidAlgebra (ZMod p) Q)).subtype)) = 1
  rw [aug_comap_one_bot]
  -- quotient by zero
  rw [(Submodule.quotEquivOfEqBot (⊥ : Submodule (ZMod p)
       (↥(1 : Submodule (ZMod p) (MonoidAlgebra (ZMod p) Q)))) rfl).finrank_eq]
  -- the scalar line is the range of the algebra map
  have hinj : Function.Injective
       (Algebra.linearMap (ZMod p) (MonoidAlgebra (ZMod p) Q)) := by
    intro a b hab
    have hh := congrArg (eps p Q) hab
    simpa [eps, MonoidAlgebra.singleOneRingHom] using hh
  have hr := (LinearEquiv.ofInjective
      (Algebra.linearMap (ZMod p) (MonoidAlgebra (ZMod p) Q)) hinj).finrank_eq
  -- its range is `1`
  rw [← Submodule.one_eq_range] at hr
  simpa [Module.finrank_self (ZMod p)] using hr.symm
end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Nilpotence.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/PrefixArithmetic.lean
section
open scoped BigOperators
open Polynomial Finset
noncomputable section

/-- Finite real power series with nonnegative initial partial sums is
nonnegative on `[0,1]`.  This is the elementary summation-by-parts
replacement for coefficientwise positivity. -/
lemma sum_mul_pow_nonneg_of_prefix (c : ℕ → ℝ) (N : ℕ)
    {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hs : ∀ m : ℕ, 0 ≤ ∑ i ∈ Finset.range (m+1), c i) :
    0 ≤ ∑ i ∈ Finset.range N, c i * t^i := by
  let ss : ℕ → ℝ := fun i => ∑ j ∈ Finset.range (i+1), c j
  have ss_succ (i : ℕ) : ss (i+1) = ss i + c (i+1) := by
    simp [ss, Finset.sum_range_succ]
  have hparts (M : ℕ) :
      (∑ i ∈ Finset.range (M+1), c i * t^i) =
        (∑ i ∈ Finset.range M,
          ss i * (t^i - t^(i+1))) + ss M * t^M := by
    induction M with
    | zero => simp [ss]
    | succ M ih =>
      calc
        (∑ i ∈ Finset.range (M+1+1), c i * t^i) =
            (∑ i ∈ Finset.range (M+1), c i * t^i) + c (M+1)*t^(M+1) := by rw [Finset.sum_range_succ]
        _ = ( (∑ i ∈ Finset.range M, ss i * (t^i-t^(i+1))) + ss M*t^M) + c (M+1)*t^(M+1) := by rw [ih]
        _ = (∑ i ∈ Finset.range (M+1), ss i * (t^i-t^(i+1))) + ss (M+1)*t^(M+1) := by
          rw [Finset.sum_range_succ, ss_succ]
          ring

  rcases N with _ | M
  · simp
  · rw [hparts]
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro i hi
      have hs' := hs i
      have hpow : 0 ≤ t^i - t^(i+1) := by
        rw [pow_succ]
        have hh : 0 ≤ t^i := pow_nonneg h0 i
        nlinarith
      change 0 ≤ ss i * _
      exact mul_nonneg hs' hpow
    · change 0 ≤ ss M * _
      exact mul_nonneg (hs M) (pow_nonneg h0 M)

/-- Prefix version of the elementary GS power-series argument. It suffices
that the *partial sums* of `a_{n+2}- d a_{n+1}+r a_n` are nonnegative.
The radius point `2/d` lies in `[0,1]` as soon as `2 ≤ d`.
This formulation is useful with intersection (rather than strict) filtrations. -/
theorem numerical_gs_prefix_nat (d r : ℕ) (hd : 2 ≤ d)
    (a : ℕ → ℕ) (ha0 : a 0 = 1) (ha1 : a 1 = d)
    (hfin : ∃ N : ℕ, ∀ n ≥ N, a n = 0)
    (hstep : ∀ m : ℕ,
      d * (∑ i ∈ Finset.range (m+1), a (i+1)) ≤
        (∑ i ∈ Finset.range (m+1), a (i+2)) +
          r * (∑ i ∈ Finset.range (m+1), a i)) :
    (d : ℝ)^2 < 4 * (r : ℝ) := by
  classical
  by_contra! hbad
  obtain ⟨N, hN⟩ := hfin
  let ar : ℕ → ℝ := fun n => (a n : ℝ)
  have hNr : ∀ n ≥ N, ar n = 0 := by
    intro n hn; simp [ar, hN n hn]
  let cc : ℕ → ℝ := fun n => ar (n+2) - (d:ℝ) * ar (n+1) + (r:ℝ)* ar n
  have hccN : ∀ n ≥ N, cc n = 0 := by
    intro n hn
    have h0' := hNr n hn
    have h1' := hNr (n+1) (by omega)
    have h2' := hNr (n+2) (by omega)
    dsimp [cc]
    rw [h0', h1', h2']
    ring
  have hprefix : ∀ m : ℕ, 0 ≤ ∑ i ∈ Finset.range (m+1), cc i := by
    intro m
    have h := hstep m
    have hh : (d:ℝ) * (∑ i ∈ Finset.range (m+1), ar (i+1)) ≤
        (∑ i ∈ Finset.range (m+1), ar (i+2)) +
          (r:ℝ) * (∑ i ∈ Finset.range (m+1), ar i) := by
      -- cast the finite natural equality/inequality once; the casts of the
      -- bounded sums are harmless and avoid truncated subtraction.
      dsimp [ar]
      simp_rw [← Nat.cast_sum]
      norm_cast
    dsimp [cc]
    -- distribute the real sums; now every summand is literal.
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    -- convert sums with constant multipliers
    have hdistr1 :
        (∑ i ∈ Finset.range (m+1), (d:ℝ) * ar (i+1)) =
          (d:ℝ) * (∑ i ∈ Finset.range (m+1), ar (i+1)) := by
        rw [Finset.mul_sum]
    have hdistr2 :
        (∑ i ∈ Finset.range (m+1), (r:ℝ) * ar i) =
          (r:ℝ) * (∑ i ∈ Finset.range (m+1), ar i) := by
        rw [Finset.mul_sum]
    rw [hdistr1, hdistr2]
    linarith
  let A : ℝ[X] := ∑ i ∈ Finset.range N, Polynomial.monomial i (ar i)
  let Cc : ℝ[X] := ∑ i ∈ Finset.range N, Polynomial.monomial i (cc i)
  let q : ℝ[X] := 1 - Polynomial.C (d:ℝ) * Polynomial.X +
        Polynomial.C (r:ℝ) * Polynomial.X ^ 2
  have hAcoeff (n : ℕ) : A.coeff n = ar n := by
    dsimp [A]
    exact coeff_finpoly ar hNr n
  have hCcoeff (n : ℕ) : Cc.coeff n = cc n := by
    dsimp [Cc]
    exact coeff_finpoly cc hccN n
  -- Coefficient identities at 0 and 1 together with the shifted tail
  -- package the whole convolution as `1 + X^2 C`.
  have hpoly : q * A = 1 + Polynomial.X^2 * Cc := by
    ext n
    rcases n with (_ | n)
    · dsimp [q, A]
      rw [qA_coeff_zero ar hNr (d:ℝ) (r:ℝ)]
      simp [ar, ha0]
    · rcases n with (_ | n)
      · dsimp [q, A]
        rw [qA_coeff_one ar hNr (d:ℝ) (r:ℝ)]
        simp [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', Polynomial.coeff_one, ar, ha0, ha1]
      · dsimp [q, A]
        rw [qA_coeff_two_add ar hNr (d:ℝ) (r:ℝ) n]
        -- the RHS has no constant coefficient in degree `n+2`
        simp [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', hCcoeff,
          cc, Polynomial.coeff_one]
  let t : ℝ := 2 / (d:ℝ)
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2:ℕ)) hd)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ hd0).2
    norm_num
    exact_mod_cast hd
  have hCe : 0 ≤ Cc.eval t := by
    -- evaluate the finite polynomial before applying summation by parts
    dsimp [Cc]
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    -- `eval_monomial` presents `t^i * cc i`; switch their order.
    have hs := sum_mul_pow_nonneg_of_prefix cc N ht0 ht1 hprefix
    -- `simp` usually chooses the opposite order
    simpa [mul_comm] using hs
  have hAe : 0 ≤ A.eval t := by
    dsimp [A]
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (by dsimp [ar]; exact_mod_cast (Nat.zero_le (a i))) (pow_nonneg ht0 i)
  have hqe : q.eval t = 1 - (d:ℝ)*t + (r:ℝ)*t^2 := by
    dsimp [q]
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow]
  have hq0 : q.eval t ≤ 0 := by
    rw [hqe]
    dsimp [t]
    have hne : (d:ℝ) ≠ 0 := ne_of_gt hd0
    field_simp
    nlinarith
  have hupper : (q*A).eval t ≤ 0 := by
    rw [Polynomial.eval_mul]
    exact mul_nonpos_of_nonpos_of_nonneg hq0 hAe
  have hlower : (1:ℝ) ≤ (q*A).eval t := by
    rw [hpoly]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]
    linarith [mul_nonneg (by positivity : 0 ≤ t^2) hCe]
  linarith

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/PrefixArithmetic.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/FirstDegree.lean
section
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace GSsupport
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

def delta (q : Q) : B := MonoidAlgebra.of k Q q - 1

@[simp] lemma eps_of (q:Q) : eps p Q (MonoidAlgebra.of k Q q) = 1 := by
  change (MonoidAlgebra.lift k k Q (1 : Q →* k)) (MonoidAlgebra.single q 1) = 1
  simp [MonoidAlgebra.lift_single]

@[simp] lemma eps_delta (q:Q) : eps p Q (delta p Q q) = 0 := by
  have h := eps_of p Q q
  -- reveal the basis element as a single
  change (eps p Q) (MonoidAlgebra.single q 1) = 1 at h
  simp [delta, h]

def deltaJ (q:Q) : aug p Q := ⟨delta p Q q, eps_delta p Q q⟩

-- temporary simple layer with powers simplified
abbrev oneRel : Submodule k (aug p Q) :=
   (aug p Q ^ 2).comap (aug p Q).subtype
abbrev oneLayer : Type _ := (aug p Q) ⧸ (oneRel p Q)

def delta1 (q:Q) : oneLayer p Q :=
  Submodule.Quotient.mk (deltaJ p Q q)

-- equivalence with augLayer 1; preferably reducible via simp
noncomputable def oneLayerEquiv : augLayer p Q 1 ≃ₗ[k] oneLayer p Q := by
  unfold augLayer
  rw [pow_one (aug p Q)]

-- augCoeffs one equal finrank oneLayer
lemma augCoeffs_one_eq : augCoeffs p Q 1 = Module.finrank k (oneLayer p Q) := by
  unfold augCoeffs
  exact (oneLayerEquiv p Q).finrank_eq

end GSsupport

namespace GSsupport
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

lemma sum_of (x : B) :
    x.sum (fun q c => c • (MonoidAlgebra.of k Q q : B)) = x := by
  simpa [MonoidAlgebra.of_apply, Finsupp.smul_single] using (Finsupp.sum_single x)

lemma eps_sum (x : B) : eps p Q x = x.sum (fun (_:Q) c => c) := by
  -- lift apply
  change (MonoidAlgebra.lift k k Q (1 : Q →* k)) x = _
  rw [MonoidAlgebra.lift_apply]
  -- action of coefficient on 1 is itself
  simp

lemma sum_smul_one (x : B) :
    x.sum (fun (_:Q) c => c • (1:B)) =
      (x.sum (fun (_:Q) c => c)) • (1:B) := by
  classical
  -- distribute scalar over finite sum
  -- use support expansion
  classical
  simp only [Finsupp.sum]
  simpa using ((Finset.sum_smul : (∑ i ∈ x.support, x i) • (1:B) = _).symm)
lemma sum_delta (x : B) :
    x.sum (fun q c => c • (delta p Q q)) = x - (eps p Q x) • (1:B) := by
  classical
  calc
    x.sum (fun q c => c • (delta p Q q)) =
       x.sum (fun q c => c • (MonoidAlgebra.of k Q q : B) - c • (1:B)) := by
         simp [delta, smul_sub]
    _ = x.sum (fun q c => c • (MonoidAlgebra.of k Q q : B)) -
         x.sum (fun (_:Q) c => c • (1:B)) := by
         -- sum of differences
         simp only [Finsupp.sum]
         exact Finset.sum_sub_distrib _ _
    _ = x - (eps p Q x) • (1:B) := by
         rw [sum_of (p:=p) (Q:=Q), sum_smul_one (p:=p) (Q:=Q), eps_sum (p:=p) (Q:=Q)]

lemma delta_span_J : Submodule.span k (Set.range (deltaJ p Q)) = ⊤ := by
  classical
  apply top_unique
  intro z hz
  -- show any element of the augmentation is sum of the deltas
  change z ∈ Submodule.span k (Set.range (deltaJ p Q))
  have hzero : eps p Q (z:B) = 0 := z.property
  have heq : ( (z:B).sum (fun q c => c • delta p Q q)) = (z:B) := by
    rw [sum_delta (p:=p) (Q:=Q), hzero]
    simp
  -- express in the submodule pointwise; use finite sum
  -- goal for subtype z; build equality of finite sums of subtype vectors
  have hzmem : ∀ (q:Q) (c:k), c • deltaJ p Q q ∈ Submodule.span k (Set.range (deltaJ p Q)) := by
    intro q c
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨q, rfl⟩
  -- express z as image of sum
  have hsum_mem : (z:B).sum (fun q c => c • deltaJ p Q q) ∈
        Submodule.span k (Set.range (deltaJ p Q)) := by
    -- expand and sum membership
    classical
    exact Submodule.sum_mem _ (fun i hi => hzmem i ((z:B) i))
  have hsum_eq : ( (z:B).sum (fun q c => c • deltaJ p Q q)) = z := by
    apply Subtype.ext
    -- coercion through sum
    -- subtype coe sum
    simp only [Finsupp.sum]
    -- coe of sums handled by commute sum subtype? try simp
    change (↑(∑ i ∈ (z:B).support, ((z:B) i) • deltaJ p Q i) : B) = (z:B)
    simpa [Finsupp.sum, deltaJ] using heq
  rwa [hsum_eq] at hsum_mem

lemma delta1_span : Submodule.span k (Set.range (delta1 p Q)) = ⊤ := by
  classical
  let f : (aug p Q) →ₗ[k] (oneLayer p Q) := (oneRel p Q).mkQ
  have himage : f '' (Set.range (deltaJ p Q)) = Set.range (delta1 p Q) := by
    ext y
    constructor
    · rintro ⟨x, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨deltaJ p Q q, ⟨q, rfl⟩, rfl⟩
  symm
  calc
    (⊤ : Submodule k (oneLayer p Q)) = f.range := by
      symm
      exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)
    _ = Submodule.map f (⊤ : Submodule k (aug p Q)) := by simp
    _ = Submodule.map f (Submodule.span k (Set.range (deltaJ p Q))) := by
      rw [delta_span_J (p:=p) (Q:=Q)]
    _ = Submodule.span k (Set.range (delta1 p Q)) := by
      rw [LinearMap.map_span, himage]



/-- The degree-one generators belonging to a finite set, as a subspace of `J`. -/
def genJspace (T : Finset Q) : Submodule k (aug p Q) :=
  Submodule.span k ((deltaJ p Q) '' (↑T : Set Q))

/-- The left subspace of the group algebra generated by the differences from `T`. -/
def genLeft (T : Finset Q) : Submodule k B :=
  (⊤ : Submodule k B) *
    (Submodule.span k ((delta p Q) '' (↑T : Set Q)))

lemma genLeft_of_gen (T : Finset Q) {q : Q} (hq : q ∈ T) :
    delta p Q q ∈ genLeft p Q T := by
  change delta p Q q ∈ (⊤ : Submodule k B) *
    (Submodule.span k ((delta p Q) '' (↑T : Set Q)))
  -- write it as 1 times the generator
  have hd : delta p Q q ∈ Submodule.span k ((delta p Q) '' (↑T : Set Q)) :=
    Submodule.subset_span ⟨q, by simpa using hq, rfl⟩
  have ho : (1:B) ∈ (⊤ : Submodule k B) := trivial
  have hm := Submodule.mul_mem_mul ho hd
  simpa using hm

lemma genLeft_left (T : Finset Q) (a y : B)
    (hy : y ∈ genLeft p Q T) : a * y ∈ genLeft p Q T := by
  classical
  -- induction on the products defining top * the span
  change y ∈ (⊤ : Submodule k B) *
    (Submodule.span k ((delta p Q) '' (↑T : Set Q))) at hy
  change a * y ∈ (⊤ : Submodule k B) *
    (Submodule.span k ((delta p Q) '' (↑T : Set Q)))
  refine Submodule.mul_induction_on (M := (⊤ : Submodule k B))
       (N := Submodule.span k ((delta p Q) '' (↑T : Set Q))) hy ?_ ?_
  · intro b hb c hc
    have hab : a * b ∈ (⊤ : Submodule k B) := trivial
    simpa [mul_assoc] using (Submodule.mul_mem_mul hab hc)
  · intro x y hx' hy'
    simpa [mul_add] using
      (( (⊤ : Submodule k B) *
        (Submodule.span k ((delta p Q) '' (↑T : Set Q)))).add_mem hx' hy')

lemma genJ_to_left (T : Finset Q) (x : aug p Q)
    (hx : x ∈ genJspace p Q T) :
    (x : B) ∈ genLeft p Q T := by
  classical
  -- induction on the span in J
  unfold genJspace at hx
  refine Submodule.span_induction (p := fun (z : aug p Q) (_ : z ∈
      Submodule.span k ((deltaJ p Q) '' (↑T : Set Q))) =>
        (z : B) ∈ genLeft p Q T) ?_ ?_ ?_ ?_ hx
  · intro z hz
    obtain ⟨q, hq, rfl⟩ := hz
    exact genLeft_of_gen (p:=p) (Q:=Q) T hq
  · simp
  · intro x y hx hy hxx hyy
    exact (genLeft p Q T).add_mem hxx hyy
  · intro c x hx hxx
    exact (genLeft p Q T).smul_mem c hxx

lemma base_step (T : Finset Q)
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    aug p Q ≤ genLeft p Q T ⊔ (aug p Q ^ 2) := by
  classical
  let f : (aug p Q) →ₗ[k] (oneLayer p Q) := (oneRel p Q).mkQ
  have him : f '' ((deltaJ p Q) '' (↑T : Set Q)) =
      ((delta1 p Q) '' (↑T : Set Q)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨deltaJ p Q q, ⟨q, hq, rfl⟩, rfl⟩
  have hmap : Submodule.map f (genJspace p Q T) = ⊤ := by
    unfold genJspace
    rw [LinearMap.map_span, him, hspan]
  intro x hx
  -- x is in the augmentation; use a representative in genJspace
  let xx : aug p Q := ⟨x, hx⟩
  have hfmem : f xx ∈ Submodule.map f (genJspace p Q T) := by
    rw [hmap]
    trivial
  obtain ⟨z, hz, heq⟩ := hfmem
  have heq' : -(z : aug p Q) + xx ∈ oneRel p Q :=
    (Submodule.Quotient.eq' (oneRel p Q)).mp heq
  have hdiffJ : (-(z:B) + x) ∈ (aug p Q ^ 2) := heq'
  have hzL : (z:B) ∈ genLeft p Q T := genJ_to_left p Q T z hz
  -- exhibit z + (-z+x)
  apply (Submodule.mem_sup).2
  refine ⟨(z:B), hzL, (-(z:B) + x), hdiffJ, ?_⟩
  abel

lemma pow_step (T : Finset Q)
    (hbase : aug p Q ≤ genLeft p Q T ⊔ (aug p Q ^ 2)) :
    ∀ n : ℕ, aug p Q ^ (n+1) ≤ genLeft p Q T ⊔ (aug p Q ^ (n+2)) := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    -- multiply the base decomposition on the right-most factor
    -- use J^(n+1) = J^n * J, substituting hbase into the J
    -- actually direct formula for this n using J^n * J and hbase
    -- inductive result follows multiply left by J once
    -- use pow_succ' orientation J * J^(n+1), decompose the latter via ih
    rw [pow_succ' (aug p Q) (n+1)]
    intro x hx
    refine Submodule.mul_induction_on (M := aug p Q)
       (N := aug p Q ^ (n+1)) hx ?_ ?_
    · intro a ha b hb
      have hb' := ih hb
      obtain ⟨l, hl, c, hc, he⟩ := (Submodule.mem_sup).1 hb'
      -- a*l is in the left part; a*c in the remaining power
      have hal : a * l ∈ genLeft p Q T :=
        genLeft_left p Q T a l hl
      have hac : a * c ∈ aug p Q ^ (n+3) := by
        -- J * J^(n+2)
        have := Submodule.mul_mem_mul ha hc
        simpa [pow_succ'] using this
      apply (Submodule.mem_sup).2
      refine ⟨a*l, hal, a*c, hac, ?_⟩
      rw [← mul_add, he]
    · intro x y hx' hy'
      exact (genLeft p Q T ⊔ (aug p Q ^ (n+3))).add_mem hx' hy'


lemma J_le_left (T : Finset Q) (hbase : aug p Q ≤ genLeft p Q T ⊔ (aug p Q ^ 2))
    (hp : IsPGroup p Q) [Finite Q] :
    aug p Q ≤ genLeft p Q T := by
  classical
  have hs := pow_step p Q T hbase
  have hall : ∀ n : ℕ, aug p Q ≤ genLeft p Q T ⊔ (aug p Q ^ (n+1)) := by
    intro n
    induction n with
    | zero =>
      
      have : aug p Q ≤ genLeft p Q T ⊔ aug p Q := le_sup_right
      simpa using this
    | succ n ih =>
      calc
        aug p Q ≤ genLeft p Q T ⊔ (aug p Q ^ (n+1)) := ih
        _ ≤ genLeft p Q T ⊔ (genLeft p Q T ⊔ (aug p Q ^ (n+2))) :=
            sup_le_sup_left (hs n) _
        _ = genLeft p Q T ⊔ (aug p Q ^ (n+2)) := by
            simp [sup_assoc]
  obtain ⟨N, hN⟩ := aug_nilpotent p Q hp
  have hN1 : aug p Q ^ (N+1) = (⊥ : Submodule k B) := by
    rw [pow_succ, hN, Submodule.bot_mul]
  have hh := hall N
  simpa [hN1] using hh




/-- A finite subfamily of the group differences already spans degree one; it
can be chosen with at most the dimension many elements.  This is the linear
algebra part of the Burnside basis argument. -/
lemma small_span [Finite Q] : ∃ T : Finset Q,
    T.card ≤ Module.finrank k (oneLayer p Q) ∧
    Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤ := by
  classical
  -- choose a basis subset of the spanning set of all the group differences
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent k (Set.range (delta1 p Q))
  have hbfin : b.Finite := by
    letI : Fintype Q := Fintype.ofFinite Q
    exact (Set.finite_range (delta1 p Q)).subset hb
  let f : b → Q := fun x => Classical.choose (hb x.property)
  have hf (x : b) : delta1 p Q (f x) = x :=
    Classical.choose_spec (hb x.property)
  have fi : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    exact calc
      (x : oneLayer p Q) = delta1 p Q (f x) := (hf x).symm
      _ = delta1 p Q (f y) := congrArg _ hh
      _ = (y : oneLayer p Q) := hf y
  letI : Fintype b := hbfin.fintype
  let T : Finset Q := Finset.univ.map ⟨f, fi⟩
  refine ⟨T, ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_univ]
    exact LinearIndependent.fintype_card_le_finrank hli
  have heq : ((delta1 p Q) '' (↑T : Set Q)) = b := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      have : ∃ z : b, f z = q := by
        have := hq
        simp [T] at this
        obtain ⟨a, ha, e⟩ := this
        exact ⟨⟨a, ha⟩, e⟩
      obtain ⟨z, rfl⟩ := this
      have hh := hf z
      rw [hh]
      exact z.property
    · intro hx
      have hx' : (⟨x,hx⟩ : b) ∈ (Finset.univ : Finset b) := Finset.mem_univ _
      refine ⟨f ⟨x,hx⟩, ?_, ?_⟩
      · change f ⟨x,hx⟩ ∈ T
        simp [T]
      · exact hf ⟨x,hx⟩
  rw [heq, hspan]
  rw [delta1_span (p:=p) (Q:=Q)]

end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/FirstDegree.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Burnside.lean
section
noncomputable section
open scoped BigOperators
namespace GSsupport
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- Burnside's elementary coset argument, in a form which does not use the
Frattini subgroup.  If the augmentation ideal is generated, as a **left**
ideal/vector subspace, by the differences belonging to a family `T`, then
that family already generates the group.  We use the free module on the
right-`H` cosets (mathlib's `Q ⧸ H`). -/
lemma closure_of_J_le_left (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) :
    Subgroup.closure (↑T : Set Q) = ⊤ := by
  classical
  let H : Subgroup Q := Subgroup.closure (↑T : Set Q)
  let X := Q ⧸ H
  -- send a basis vector of the group algebra to its coset basis vector
  let qm : Q → X := fun q => (QuotientGroup.mk q : Q ⧸ H)
  let Phi : B →ₗ[k] (X →₀ k) := Finsupp.lmapDomain k k qm
  -- Multiplying a representative on the right by an element of `H` doesn't
  -- change its image coset.
  have qeq (a t : Q) (ht : t ∈ H) : qm (a*t) = qm a := by
    change (QuotientGroup.mk (a*t) : Q ⧸ H) =
      (QuotientGroup.mk a : Q ⧸ H)
    -- `Q ⧸ H` is the quotient for the relation `x⁻¹*y ∈ H`.
    apply (QuotientGroup.eq).2
    -- using the order `(a*t), a` in that relation
    -- gives `t⁻¹`; using symmetry is a little simpler.
    -- actually simplify directly
    have hi : t⁻¹ ∈ H := H.inv_mem ht
    -- (a*t)⁻¹*a = t⁻¹
    simpa [mul_assoc] using hi
  -- a right multiplication by a generator difference has zero coset sum.
  have kill_single (a : B) (t : Q) (ht : t ∈ H) :
      Phi (a * delta p Q t) = 0 := by
    -- prove by linear induction on `a`; on a basis vector it is just equality
    -- of the two cosets.
    induction a using Finsupp.induction_linear with
    | zero =>
        change Phi ((0 : B) * delta p Q t) = 0
        rw [zero_mul]
        exact LinearMap.map_zero Phi
    | add f g hf hg =>
        let F : B := f
        let G : B := g
        change Phi (F * delta p Q t) = 0 at hf
        change Phi (G * delta p Q t) = 0 at hg
        change Phi ((F + G) * delta p Q t) = 0
        rw [add_mul, LinearMap.map_add, hf, hg, add_zero]
    | single x c =>
        -- reveal all the basis vectors as `single`s.
        change Phi
          ((MonoidAlgebra.single x c : B) *
            (MonoidAlgebra.of k Q t - 1)) = 0
        -- mapDomain sends a `single` to the `single` of the coset.
        rw [mul_sub]
        -- first do the products, then convert the linear map to mapDomain.
        simp only [map_sub, MonoidAlgebra.of_apply, MonoidAlgebra.one_def,
          MonoidAlgebra.single_mul_single, mul_one]
        change (Finsupp.mapDomain qm (MonoidAlgebra.single (x*t) c)) -
          (Finsupp.mapDomain qm (MonoidAlgebra.single x c)) = 0
        rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, qeq x t ht]
        simp
  -- Every vector in the generated left subspace is killed by `Phi`.
  have kill_left : ∀ y : B, y ∈ genLeft p Q T → Phi y = 0 := by
    intro y hy
    change y ∈ (⊤ : Submodule k B) *
      (Submodule.span k ((delta p Q) '' (↑T : Set Q))) at hy
    refine Submodule.mul_induction_on
      (M := (⊤ : Submodule k B))
      (N := Submodule.span k ((delta p Q) '' (↑T : Set Q)))
      hy ?_ ?_
    · intro a ha c hc
      -- extend the calculation on a single difference by linearity in the
      -- right argument (`span`).
      refine Submodule.span_induction
        (p := fun (z : B) (_ : z ∈
          Submodule.span k ((delta p Q) '' (↑T : Set Q))) =>
            Phi (a * z) = 0) ?_ ?_ ?_ ?_ hc
      · intro z hz
        obtain ⟨t, ht, rfl⟩ := hz
        apply kill_single a t
        exact Subgroup.subset_closure ht
      · simp
      · intro x y hx hy hx0 hy0
        simp [mul_add, map_add, hx0, hy0]
      · intro r z hz hz0
        calc
          Phi (a * (r • z)) = Phi (r • (a * z)) := by
            rw [Algebra.mul_smul_comm]
          _ = r • Phi (a * z) := by rw [LinearMap.map_smul]
          _ = 0 := by simp [hz0]
    · intro x y hx0 hy0
      simp [map_add, hx0, hy0]
  -- hence all group differences have equal coset; the free-module basis
  -- detects equality of the underlying cosets.
  change H = ⊤
  apply top_unique
  intro q hq
  have hqJ : delta p Q q ∈ aug p Q := by
    change (eps p Q) (delta p Q q) = 0
    exact eps_delta p Q q
  have h0 : Phi (delta p Q q) = 0 :=
    kill_left _ (hleft hqJ)
  have hs : (Finsupp.single (qm q) (1:k) -
        Finsupp.single (qm (1:Q)) (1:k) : X →₀ k) = 0 := by
    change Phi ((MonoidAlgebra.single q (1:k) : B) -
        MonoidAlgebra.single (1:Q) (1:k)) = 0 at h0
    rw [LinearMap.map_sub] at h0
    change (Finsupp.mapDomain qm (MonoidAlgebra.single q (1:k))) -
      (Finsupp.mapDomain qm (MonoidAlgebra.single (1:Q) (1:k))) = 0 at h0
    simpa [Finsupp.mapDomain_single] using h0

  have heqs : (Finsupp.single (qm q) (1:k) : X →₀ k) =
        Finsupp.single (qm (1:Q)) (1:k) := sub_eq_zero.mp hs
  have heqcos : qm q = qm (1:Q) :=
    (Finsupp.single_left_injective (α:=X) (one_ne_zero : (1:k) ≠ 0)) heqs
  have hmem : (1:Q)⁻¹ * q ∈ H := by
    -- use the convenient equality criterion for `leftRel`, in the useful
    -- order `1, q`
    exact (QuotientGroup.eq).1 heqcos.symm
  simpa using hmem
end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Burnside.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Presentation.lean
section
noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- The first, entirely algebraic, arrow of the minimal resolution of the
augmented algebra.  We use functions on a finite set (rather than tensor
notation); an entry `u i` is the coefficient on the *left* of `i-1`. -/
abbrev relFree (T : Finset Q) := (i : (↥T)) → B

def relMap (T : Finset Q) : relFree p Q T →ₗ[k] B where
  toFun u := ∑ i : (↥T), u i * delta p Q i.1
  map_add' u v := by
    simp only [Pi.add_apply, add_mul]
    rw [← Finset.sum_add_distrib]
  map_smul' c u := by
    -- scalar commutes with multiplication in a group algebra
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [smul_mul_assoc]

/-- all products in the preceding arrow have augmentation zero -/
lemma relMap_mem_aug (T : Finset Q) (u : relFree p Q T) :
    relMap p Q T u ∈ aug p Q := by
  change eps p Q (∑ i : (↥T), u i * delta p Q i.1) = 0
  -- using multiplicativity of eps
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_mul, eps_delta, mul_zero]

/-- left multiplication of a vector. Keeping it explicit avoids putting an
extra algebra-module structure on the free vectors. -/
def vecMul (T : Finset Q) (a : B) (u : relFree p Q T) : relFree p Q T :=
  fun i => a * u i

lemma vecMul_add (T : Finset Q) (a b : B) (u : relFree p Q T) :
    vecMul p Q T (a+b) u = vecMul p Q T a u + vecMul p Q T b u := by
  funext i; exact add_mul _ _ _
lemma vecMul_add' (T : Finset Q) (a : B) (u v : relFree p Q T) :
    vecMul p Q T a (u+v) = vecMul p Q T a u + vecMul p Q T a v := by
  funext i; exact mul_add _ _ _
lemma vecMul_assoc (T : Finset Q) (a b : B) (u : relFree p Q T) :
    vecMul p Q T a (vecMul p Q T b u) = vecMul p Q T (a*b) u := by
  funext i; exact (mul_assoc _ _ _).symm
lemma relMap_mul (T : Finset Q) (a : B) (u : relFree p Q T) :
   relMap p Q T (vecMul p Q T a u) = a * relMap p Q T u := by
   change (∑ i : (↥T), (a * u i) * delta p Q i.1) =
     a * ∑ i : (↥T), u i * delta p Q i.1
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro i hi
   rw [mul_assoc]

/-- The standard vector with its `t`th coordinate 1. -/
noncomputable def basisVec (T : Finset Q) (t : ↥T) : relFree p Q T := by
  classical
  exact fun i => if i=t then 1 else 0
@[simp] lemma basisVec_at (T : Finset Q) (t i : ↥T) :
    basisVec p Q T t i = (if i=t then 1 else 0) := by
   classical
   simp [basisVec]
@[simp] lemma relMap_basisVec (T : Finset Q) (t : ↥T) :
    relMap p Q T (basisVec p Q T t) = delta p Q t.1 := by
  classical
  change (∑ i : (↥T), (basisVec p Q T t i) * delta p Q i.1) = _
  simp [basisVec]
@[simp] lemma vecMul_basis (T : Finset Q) (a : B) (t : ↥T) (i : ↥T) :
    vecMul p Q T a (basisVec p Q T t) i = if i=t then a else 0 := by
  classical
  by_cases h : i=t
  · subst i; simp [vecMul, basisVec]
  · simp [vecMul, basisVec, h]

/-- Every vector is the sum of its coordinates times the standard vectors. -/
lemma vec_sum (T : Finset Q) (u : relFree p Q T) :
    u = ∑ t : (↥T), vecMul p Q T (u t) (basisVec p Q T t) := by
  classical
  funext i
  classical
  simp [vecMul_basis]

/-- The range of the resolution arrow is precisely the subspace denoted
`genLeft` in `FirstDegree`.  This doesn't use finiteness of the group. -/
lemma relMap_range (T : Finset Q) :
    (relMap p Q T).range = genLeft p Q T := by
  classical
  apply le_antisymm
  · rintro x ⟨u, rfl⟩
    -- sums of left multiples of the deltas
    change (∑ i : (↥T), u i * delta p Q i.1) ∈ genLeft p Q T
    apply Submodule.sum_mem
    intro i hi
    -- product of something in top with a generator in the span
    apply Submodule.mul_mem_mul (M := (⊤ : Submodule k B))
      (N := Submodule.span k ((delta p Q) '' (↑T : Set Q))) (by trivial)
    apply Submodule.subset_span
    exact ⟨i, i.property, rfl⟩
  · -- induction on products and the span in the second factor
    intro x hx
    change x ∈ (relMap p Q T).range
    change x ∈ (⊤ : Submodule k B) *
       Submodule.span k ((delta p Q) '' (↑T : Set Q)) at hx
    refine Submodule.mul_induction_on (M := (⊤ : Submodule k B))
       (N := Submodule.span k ((delta p Q) '' (↑T : Set Q))) hx ?_ ?_
    · intro a ha b hb
      -- it suffices by linearity in `b`; keep `a` fixed.
      refine Submodule.span_induction (p := fun y (_ : y ∈
          Submodule.span k ((delta p Q) '' (↑T : Set Q))) =>
            a * y ∈ (relMap p Q T).range) ?_ ?_ ?_ ?_ hb
      · intro y hy
        obtain ⟨q, hq, rfl⟩ := hy
        let t : ↥T := ⟨q, hq⟩
        refine ⟨vecMul p Q T a (basisVec p Q T t), ?_⟩
        rw [relMap_mul, relMap_basisVec]
      · simp
      · intro y z hy hz hiy hiz
        -- range closed under addition
        rw [mul_add]
        exact (relMap p Q T).range.add_mem hiy hiz
      · intro c y hy hiy
        -- range is a submodule
        simpa [mul_smul_comm] using ((relMap p Q T).range.smul_mem c hiy)
    · intro x y hx hy
      exact (relMap p Q T).range.add_mem hx hy

/-- A set spanning the first layer with the minimal possible cardinality is in
fact a basis of that layer. This is the only independence fact about the set
chosen in `small_span` that is needed for the presentation. -/
lemma selected_independent [Finite Q] (T : Finset Q)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    LinearIndependent k (fun t : ↥T => delta1 p Q t.1) := by
  classical
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
      (R := k) (M := oneLayer p Q)
  · -- the two ways of naming this finite family
    have he : Set.range (fun t : ↥T => delta1 p Q t.1) =
        (delta1 p Q) '' (↑T : Set Q) := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t.1, t.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩
    rw [he, hspan]
  · simpa using hcard

/-- Removing the augmentation from a coefficient does not change its product
with a degree-one generator, in `J/J²`. This useful elementary computation is
usually the first line of the minimal-presentation proof. -/
lemma coeff_delta_mod_sq (a : B) (q : Q) :
  -( ((eps p Q a) • (deltaJ p Q q))) +
      (⟨a * delta p Q q, by
        change eps p Q (a * delta p Q q) = 0
        rw [map_mul, eps_delta, mul_zero]⟩ : aug p Q)
       ∈ oneRel p Q := by
  classical
  -- product of (a-eps(a)) in J with delta in J
  let w : B := a - (eps p Q a) • (1:B)
  have hw : w ∈ aug p Q := by
    change eps p Q (a - (eps p Q a) • (1:B)) = 0
    simp
  have hd : delta p Q q ∈ aug p Q := eps_delta p Q q
  have hprod : w * delta p Q q ∈ aug p Q ^ 2 := by
    -- `J^2 = J*J`
    simpa [pow_two] using (Submodule.mul_mem_mul hw hd)
  -- equality of representatives
  change (-( (eps p Q a) • (delta p Q q)) +
       a * delta p Q q) ∈ aug p Q ^ 2
  -- the displayed vector is w*delta
  convert hprod using 1 <;> dsimp [w]
  -- expand; scalar multiplication commutes with product
  simp [sub_mul, smul_mul_assoc]
  abel

/-- A linear relation between the first minimal generators has all its
coefficients in the augmentation ideal. In other words the first arrow of the
presentation is minimal: its kernel is contained in `J B^T`. -/
lemma relKernel_coordinates [Finite Q] (T : Finset Q)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤)
    (u : relFree p Q T) (hu : relMap p Q T u = 0) :
    ∀ i, u i ∈ aug p Q := by
  classical
  have hLI := selected_independent p Q T hcard hspan
  -- Reduce the equation modulo `J²`.
  have hsum : (∑ i : (↥T), (eps p Q (u i)) • (delta1 p Q i.1)) = 0 := by
    -- in the quotient, each coefficient can be replaced by its augmentation
    let mq : aug p Q →ₗ[k] (oneLayer p Q) := (oneRel p Q).mkQ
    have hbig : ∀ i : (↥T),
        (mq ⟨u i * delta p Q i.1, by
          change eps p Q (u i * delta p Q i.1) = 0
          rw [map_mul, eps_delta, mul_zero]⟩) =
          (eps p Q (u i)) • delta1 p Q i.1 := by
      intro i
      -- equality in the quotient is exactly membership of their difference
      -- in `J²`
      have hh := coeff_delta_mod_sq p Q (u i) i.1
      -- quotient equality orientation
      exact (Submodule.Quotient.eq' (oneRel p Q)).2 hh |>.symm
    calc
      (∑ i : (↥T), (eps p Q (u i)) • delta1 p Q i.1) =
          ∑ i : (↥T), mq ⟨u i * delta p Q i.1, by
            change eps p Q (u i * delta p Q i.1) = 0
            rw [map_mul, eps_delta, mul_zero]⟩ := by
              apply Finset.sum_congr rfl
              intro i hi
              exact (hbig i).symm
      _ = mq ⟨∑ i : (↥T), u i * delta p Q i.1,
              (relMap_mem_aug p Q T u)⟩ := by
              -- linear maps commute with the finite sum; first make the equality
              -- inside the subtype explicit, because the proofs of membership
              -- in `J` differ.
              have he :
                (⟨∑ i : (↥T), u i * delta p Q i.1,
                    (relMap_mem_aug p Q T u)⟩ : aug p Q) =
                  ∑ i : (↥T),
                    (⟨u i * delta p Q i.1, by
                       change eps p Q (u i * delta p Q i.1) = 0
                       rw [map_mul, eps_delta, mul_zero]⟩ : aug p Q) := by
                     apply Subtype.ext
                     simp
              rw [he, map_sum]
      _ = 0 := by
              have h' : (∑ i : (↥T), u i * delta p Q i.1) = (0:B) := hu
              have he :
                (⟨∑ i : (↥T), u i * delta p Q i.1,
                    (relMap_mem_aug p Q T u)⟩ : aug p Q) = 0 := by
                   apply Subtype.ext
                   exact h'
              rw [he, map_zero]
  have hz : ∀ i : (↥T), eps p Q (u i) = 0 :=
    (Fintype.linearIndependent_iff.mp hLI) _ hsum
  intro i
  exact hz i

/-- If the left ideal generated by `T` is all of `J`, every element `q-1`
has a chosen lift to the first free module.  This is the strict finite
analogue of the first step in a completed presentation. -/
lemma relMap_surjects_J (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) :
    ∀ z : aug p Q, ∃ v : relFree p Q T, relMap p Q T v = (z : B) := by
  classical
  intro z
  have hz : (z:B) ∈ (relMap p Q T).range := by
    rw [relMap_range p Q T]
    exact hleft z.property
  exact hz
end GSsupport
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

lemma delta_mul_formula (q r : Q) :
    delta p Q (q*r) = delta p Q q +
       (MonoidAlgebra.of k Q q : B) * delta p Q r := by
  -- keep the group elements opaque for the noncommutative-ring identity
  calc
    delta p Q (q*r) = (MonoidAlgebra.of k Q q : B) *
          (MonoidAlgebra.of k Q r : B) - 1 := by rw [delta, map_mul]
    _ = delta p Q q +
          (MonoidAlgebra.of k Q q : B) * delta p Q r := by
          dsimp [delta]
          noncomm_ring

/-- A preferred lift of `[q]-1` to the first free module. On the selected
minimal generators it is the corresponding basis vector. -/
noncomputable def genLiftVec (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (q : Q) : relFree p Q T := by
  classical
  by_cases hq : q ∈ T
  · exact basisVec p Q T ⟨q, hq⟩
  · let z : aug p Q := deltaJ p Q q
    exact Classical.choose (relMap_surjects_J p Q T hleft z)

@[simp] lemma relMap_genLiftVec (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (q : Q) :
    relMap p Q T (genLiftVec p Q T hleft q) = delta p Q q := by
  classical
  unfold genLiftVec
  split_ifs with hq
  · simpa using (relMap_basisVec p Q T ⟨q,hq⟩)
  · exact Classical.choose_spec
       (relMap_surjects_J p Q T hleft (deltaJ p Q q))

@[simp] lemma genLiftVec_selected (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (t : ↥T) :
    genLiftVec p Q T hleft t.1 = basisVec p Q T t := by
  classical
  unfold genLiftVec
  simp [t.property]

/-- Linear extension of the preferred section on group elements. It is not a
section on all of `B`, but its image under `relMap` is the elementary projection
`a ↦ a - ε(a)`. -/
noncomputable def genLiftLinear (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) : B →ₗ[k] relFree p Q T := by
  classical
  exact Finsupp.lsum k (fun q =>
    LinearMap.toSpanSingleton k _ (genLiftVec p Q T hleft q))

@[simp] lemma genLiftLinear_single (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (q : Q) (c : k) :
    genLiftLinear p Q T hleft (MonoidAlgebra.single q c) =
       c • genLiftVec p Q T hleft q := by
  classical
  unfold genLiftLinear
  change ((Finsupp.lsum k) (fun q =>
      LinearMap.toSpanSingleton k _ (genLiftVec p Q T hleft q)))
      (Finsupp.single q c) = _
  rw [Finsupp.lsum_single]
  rfl

@[simp] lemma genLiftLinear_of (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (q : Q) :
    genLiftLinear p Q T hleft (MonoidAlgebra.of k Q q) =
       genLiftVec p Q T hleft q := by
  classical
  change genLiftLinear p Q T hleft (MonoidAlgebra.single q 1) = _
  simp

lemma relMap_genLiftLinear (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (a : B) :
    relMap p Q T (genLiftLinear p Q T hleft a) = a - (eps p Q a) • (1:B) := by
  classical
  -- both sides are linear in the coefficients of `a`
  classical
  calc
    relMap p Q T (genLiftLinear p Q T hleft a)
        = a.sum (fun q c => c • delta p Q q) := by
            classical
            -- commute the two linear maps through a finsupp sum
            change relMap p Q T
                ((Finsupp.lsum k (fun q =>
                   LinearMap.toSpanSingleton k _ (genLiftVec p Q T hleft q))) a) = _
            rw [Finsupp.lsum_apply]
            change relMap p Q T
                (a.sum (fun q c => c • genLiftVec p Q T hleft q)) = _
            simp only [Finsupp.sum]
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro q hq
            simp [relMap_genLiftVec]
    _ = a - (eps p Q a) • (1:B) := sum_delta p Q a

/-- The usual two-bar in the relation module. -/
def barRelation (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (q r : Q) : relFree p Q T :=
   genLiftVec p Q T hleft q +
     vecMul p Q T (MonoidAlgebra.of k Q q) (genLiftVec p Q T hleft r) -
       genLiftVec p Q T hleft (q*r)

@[simp] lemma relMap_barRelation (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (q r : Q) :
    relMap p Q T (barRelation p Q T hleft q r) = 0 := by
  classical
  simp [barRelation, relMap_genLiftVec, relMap_mul,
    delta_mul_formula]

/-- A slightly larger, but very convenient, family of relations. They say that
multiplying a selected basis vector and then projecting back with the section
has no kernel-free part. The second argument can be any element of the group
algebra. -/
def elementaryRelation (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (a : B) (t : ↥T) : relFree p Q T :=
  vecMul p Q T a (basisVec p Q T t) -
    genLiftLinear p Q T hleft (a * delta p Q t.1)

@[simp] lemma relMap_elementaryRelation (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (a : B) (t : ↥T) :
    relMap p Q T (elementaryRelation p Q T hleft a t) = 0 := by
  classical
  -- `a*(t-1)` has augmentation zero
  have hz : eps p Q (a * delta p Q t.1) = 0 := by
    rw [map_mul, eps_delta, mul_zero]
  simp [elementaryRelation, relMap_mul, relMap_basisVec,
        relMap_genLiftLinear, hz]

/-- Every vector in the kernel is a sum of the elementary relations.  This is
an exactness proof at the middle of the first two bar terms, and is often
useful without any completed group algebra. -/
lemma kernel_sum_elementary (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (u : relFree p Q T)
    (hu : relMap p Q T u = 0) :
    u = ∑ t : (↥T), elementaryRelation p Q T hleft (u t) t := by
  classical
  -- expand `u` in the chosen standard basis. The section of the total
  -- `relMap u` cancels.
  have hs :
      (∑ t : (↥T), genLiftLinear p Q T hleft (u t * delta p Q t.1)) = 0 := by
    rw [← map_sum]
    have h' : (∑ t : (↥T), u t * delta p Q t.1) = (0:B) := hu
    rw [h']
    simp
  calc
    u = ∑ t : (↥T), vecMul p Q T (u t) (basisVec p Q T t) :=
        vec_sum p Q T u
    _ = (∑ t : (↥T), vecMul p Q T (u t) (basisVec p Q T t)) - 0 := by simp
    _ = (∑ t : (↥T), vecMul p Q T (u t) (basisVec p Q T t)) -
          (∑ t : (↥T), genLiftLinear p Q T hleft (u t * delta p Q t.1)) := by rw [hs]
    _ = _ := by simp [elementaryRelation, Finset.sum_sub_distrib]
end GSsupport
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- On a group-basis coefficient the elementary relation is just a two-bar. -/
lemma elementary_of (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (q : Q) (t : ↥T) :
    elementaryRelation p Q T hleft (MonoidAlgebra.of k Q q) t =
       barRelation p Q T hleft q t.1 := by
  classical
  -- evaluate the section on `q (t-1) = qt-q`
  have hm : (MonoidAlgebra.of k Q q : B) * delta p Q t.1 =
       (MonoidAlgebra.of k Q (q*t.1) : B) -
         (MonoidAlgebra.of k Q q : B) := by
     dsimp [delta]
     rw [mul_sub, mul_one, ← map_mul]
  unfold elementaryRelation barRelation
  rw [hm, map_sub, genLiftLinear_of, genLiftLinear_of,
      genLiftVec_selected]
  abel

/-- The elementary relations are linear in the coefficient. Packaging these
identities avoids coefficient rearrangements in later bar arguments. -/
lemma elementary_add (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (a b : B) (t : ↥T) :
    elementaryRelation p Q T hleft (a+b) t =
      elementaryRelation p Q T hleft a t +
      elementaryRelation p Q T hleft b t := by
  classical
  simp [elementaryRelation, add_mul, vecMul_add]
  abel
lemma elementary_smul (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (c : k) (a : B) (t : ↥T) :
    elementaryRelation p Q T hleft (c • a) t =
      c • elementaryRelation p Q T hleft a t := by
  classical
  -- pointwise for the first vector; the others are linear
  unfold elementaryRelation
  have hv : vecMul p Q T (c • a) (basisVec p Q T t) =
      c • (vecMul p Q T a (basisVec p Q T t)) := by
        funext i
        change (c • a) * basisVec p Q T t i =
             c • (a * basisVec p Q T t i)
        simp
  rw [hv]
  simp [smul_sub]

/-- Consequently all kernel vectors are in the linear span of the two-bars
`[q|t]`, already with `t` in the selected generating set. This finite,
explicit exactness statement is useful when comparing to degree-two
cochains. -/
lemma kernel_span_bars (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (u : relFree p Q T) (hu : relMap p Q T u = 0) :
    u ∈ Submodule.span k (Set.range
       (fun z : Q × (↥T) => barRelation p Q T hleft z.1 z.2.1)) := by
  classical
  let W := Submodule.span k (Set.range
       (fun z : Q × (↥T) => barRelation p Q T hleft z.1 z.2.1))
  have hbase (q : Q) (t : ↥T) :
      elementaryRelation p Q T hleft (MonoidAlgebra.of k Q q) t ∈ W := by
    rw [elementary_of p Q T hleft q t]
    apply Submodule.subset_span
    exact ⟨(q,t), rfl⟩
  have hall (a : B) (t : ↥T) : elementaryRelation p Q T hleft a t ∈ W := by
    -- expand the group algebra element
    have : a = a.sum (fun q c => c • (MonoidAlgebra.of k Q q : B)) :=
       (sum_of p Q a).symm
    -- use induction on the support via its expansion; easier a span argument,
    -- because the group basis spans the whole group algebra.
    classical
    -- rewrite and prove the corresponding finite sum identity by additivity
    -- of `elementaryRelation`.
    -- define a temporary linear map in the coefficient slot
    let L : B →ₗ[k] relFree p Q T :=
    { toFun := fun b => elementaryRelation p Q T hleft b t
      map_add' := fun a b => elementary_add p Q T hleft a b t
      map_smul' := by
        intro c a
        exact elementary_smul p Q T hleft c a t }
    change L a ∈ W
    rw [this]
    simp only [Finsupp.sum]
    rw [map_sum]
    apply Submodule.sum_mem
    intro q hq
    -- map of a scalar multiple
    rw [map_smul]
    exact W.smul_mem _ (hbase q t)
  rw [kernel_sum_elementary p Q T hleft u hu]
  exact Submodule.sum_mem _ (fun i hi => hall (u i) i)
end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Presentation.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Filtration.lean
section
noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- Right stability; complements `LeftInv` from the nilpotence layer.  The powers of the
augmentation subspace are two-sided.  Keeping this as a statement about submodules,
rather than ideals, is helpful since `Submodule.mul` is the product used in the definition
of `augLayer`. -/
def RightInv (W : Submodule k B) : Prop :=
  ∀ (q : Q) (x : B), x ∈ W → x * (MonoidAlgebra.of k Q q) ∈ W

lemma aug_rightInv : RightInv p Q (aug p Q) := by
  intro q x hx
  change eps p Q (x * MonoidAlgebra.of k Q q) = 0
  change eps p Q x = 0 at hx
  rw [map_mul, hx, zero_mul]

lemma pow_rightInv (n : ℕ) : RightInv p Q (aug p Q ^ (n+1)) := by
  induction n with
  | zero => simpa using (aug_rightInv p Q)
  | succ n ih =>
    rw [pow_succ']
    intro q x hx
    -- Here the last factor has exponent `n+1`. Multiplying a product on the
    -- right keeps that factor in the corresponding power.
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [mul_assoc]
      exact Submodule.mul_mem_mul ha (ih q b hb)
    · intro x y hx hy
      simpa [add_mul] using
        ((aug p Q * aug p Q ^ (n+1)).add_mem hx hy)

/-- Right multiplication by an arbitrary group-algebra element preserves a right stable
subspace. The induction has only sums and scalar multiples because the group elements are
a basis of a monoid algebra. -/
lemma all_right (W : Submodule k B) (hW : RightInv p Q W)
    (x a : B) (hx : x ∈ W) : x * a ∈ W := by
  induction a using MonoidAlgebra.induction_on with
  | hM q => exact hW q x hx
  | hadd a b ha hb => simpa [mul_add] using W.add_mem ha hb
  | hsmul r a ha =>
      -- the coefficient ring is central in a monoid algebra.
      simpa [mul_smul_comm] using W.smul_mem r ha

/-- A vector with all its entries in `J^m`. We use functions on the finite set `T`, as for
`relFree`; the honest subtype makes the later kernels and dimensions painless. -/
def freePow (T : Finset Q) (m : ℕ) : Submodule k (relFree p Q T) :=
{ carrier := {u | ∀ i, u i ∈ aug p Q ^ m}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro u v hu hv i
    exact (aug p Q ^ m).add_mem (hu i) (hv i)
  smul_mem' := by
    intro c u hu i
    exact (aug p Q ^ m).smul_mem c (hu i) }

@[simp] lemma mem_freePow (T : Finset Q) (m : ℕ) (u : relFree p Q T) :
    u ∈ freePow p Q T m ↔ ∀ i, u i ∈ aug p Q ^ m := Iff.rfl

/-- The successive positive powers descend. `Submodule.mul` uses the scalar
subspace in degree zero, so the first descending assertion starts with `J` and `J²`. -/
lemma pow_antitone_succ (m : ℕ) : aug p Q ^ (m+2) ≤ aug p Q ^ (m+1) := by
  rw [show m+2 = (m+1)+1 by omega, pow_succ]
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    exact all_right p Q (aug p Q ^ (m+1)) (pow_rightInv p Q m)
      a b ha
  · intro x y hx hy
    exact (aug p Q ^ (m+1)).add_mem hx hy

/-- Applying the first presentation arrow to coefficients in `J^m` raises
filtration by one. We restrict to positive `m`; these are exactly the steps
in the desired recurrence. -/
lemma relMap_mem_pow (T : Finset Q) (m : ℕ) (u : relFree p Q T)
    (hu : u ∈ freePow p Q T (m+1)) :
    relMap p Q T u ∈ aug p Q ^ (m+2) := by
  classical
  have hdeg : ∀ i : (↥T),
      u i * delta p Q i.1 ∈ aug p Q ^ (m+1) * aug p Q := by
    intro i
    exact Submodule.mul_mem_mul (hu i) (eps_delta p Q i.1)
  -- powers multiply on the right
  have hsum : (∑ i : (↥T), u i * delta p Q i.1) ∈
      aug p Q ^ (m+1) * aug p Q :=
    Submodule.sum_mem _ (fun i hi => hdeg i)
  change (∑ i : (↥T), u i * delta p Q i.1) ∈ aug p Q ^ (m+2)
  have he : aug p Q ^ (m+1) * aug p Q = aug p Q ^ (m+2) := by
    have hh := (pow_succ (aug p Q) (m+1)).symm
    -- avoid rewriting the exponent on the left while simplifying the right hand side
    simpa [show m+2 = (m+1)+1 by omega] using hh
  rw [← he]
  exact hsum

/-- The restricted arrow `J^(m+1)^T -> J^(m+2)`. -/
def stepMap (T : Finset Q) (m : ℕ) :
    (freePow p Q T (m+1)) →ₗ[k] (↥(aug p Q ^ (m+2))) :=
{ toFun := fun u => ⟨relMap p Q T (u : relFree p Q T),
      relMap_mem_pow p Q T m u.1 u.2⟩
  map_add' := by
    intro u v
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' := by
    intro c u
    apply Subtype.ext
    exact map_smul _ _ _ }

@[simp] lemma stepMap_val (T : Finset Q) (m : ℕ)
    (u : (freePow p Q T (m+1))) :
    ((stepMap p Q T m u : (↥(aug p Q ^ (m+2)))) : B) =
        relMap p Q T (u : relFree p Q T) := rfl

/-- The equalities `relMap.range = J` and two-sidedness make the restricted
map onto in each positive degree. This is an honest (non-associated-graded)
strictness statement, useful independently of cohomology. -/
lemma stepMap_surjective (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (m : ℕ) :
    Function.Surjective (stepMap p Q T m) := by
  classical
  intro z
  -- write a vector for a product in `J^(m+1) * J`
  have hpow : (z : B) ∈ aug p Q ^ (m+1) * aug p Q := by
    have hz : (z:B) ∈ aug p Q ^ (m+2) := z.property
    simpa [show m+2 = (m+1)+1 by omega, pow_succ] using hz
  -- induction on the definition of a product of submodules. The predicate is
  -- phrased with the equality in `B` so it has the addition closure required
  -- by `Submodule.mul_induction_on`.
  have liftprod : ∀ x : B, x ∈ aug p Q ^ (m+1) * aug p Q →
      ∃ v : relFree p Q T,
        (∀ i, v i ∈ aug p Q ^ (m+1)) ∧ relMap p Q T v = x := by
    intro x hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨w, hw⟩ := relMap_surjects_J p Q T hleft ⟨b, hb⟩
      refine ⟨vecMul p Q T a w, ?_, ?_⟩
      · intro i
        change a * w i ∈ aug p Q ^ (m+1)
        exact all_right p Q (aug p Q ^ (m+1)) (pow_rightInv p Q m)
          a (w i) ha
      · rw [relMap_mul, hw]
    · intro x y hx hy
      obtain ⟨v, hv, hve⟩ := hx
      obtain ⟨w, hw, hwe⟩ := hy
      refine ⟨v+w, ?_, ?_⟩
      · intro i
        exact (aug p Q ^ (m+1)).add_mem (hv i) (hw i)
      · simpa [hve, hwe] using (map_add (relMap p Q T) v w)
  obtain ⟨v, hv, hve⟩ := liftprod (z:B) hpow
  refine ⟨⟨v, hv⟩, ?_⟩
  apply Subtype.ext
  exact hve

/-- The kernel dimension at this step of the filtered presentation.  This is
the one missing comparison with `H^2` in the GS argument; keeping the number
as a named, entirely algebraic object prevents any ambiguity about filtrations. -/
noncomputable def stepKernelRank (T : Finset Q) (m : ℕ) : ℕ :=
  Module.finrank k (LinearMap.ker (stepMap p Q T m))


/-- Reordering the two subtypes identifies a vector of power entries with a
finite product of the corresponding power. -/
noncomputable def freePowEquiv (T : Finset Q) (m : ℕ) :
    (freePow p Q T m) ≃ₗ[k] ((i : (↥T)) → (↥(aug p Q ^ m))) :=
{ toFun := fun u i => ⟨(u.1 i), u.2 i⟩
  invFun := fun v => ⟨fun i => (v i : B), fun i => (v i).property⟩
  left_inv := by intro u; rfl
  right_inv := by intro v; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl }

lemma finrank_freePow [Finite Q] (T : Finset Q) (m : ℕ) :
    Module.finrank k (freePow p Q T m) =
       T.card * Module.finrank k (↥(aug p Q ^ m)) := by
  classical
  -- finite dimensionality follows at once from `Q` finite.
  rw [(freePowEquiv p Q T m).finrank_eq]
  rw [Module.finrank_pi_fintype]
  simp [Fintype.card_coe, Finset.mul_sum]

lemma finrank_step [Finite Q] (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (m : ℕ) :
    Module.finrank k (↥(aug p Q ^ (m+2))) + stepKernelRank p Q T m =
      Module.finrank k (freePow p Q T (m+1)) := by
  classical
  -- rank/nullity for the onto restricted map
  have hr := LinearMap.finrank_range_add_finrank_ker (stepMap p Q T m)
  have he : Module.finrank k (↥(LinearMap.range (stepMap p Q T m))) =
        Module.finrank k (↥(aug p Q ^ (m+2))) := by
    have htop : LinearMap.range (stepMap p Q T m) = ⊤ :=
       LinearMap.range_eq_top.mpr (stepMap_surjective p Q T hleft m)
    rw [htop]
    simp
  unfold stepKernelRank
  rw [← he]
  exact hr

/-- Positive adjacent powers, in the language `augCoeffs` uses for the
quotient. This elementary equality avoids any subtraction of naturals. -/
lemma coeff_finrank_pow [Finite Q] (m : ℕ) :
    augCoeffs p Q (m+1) + Module.finrank k (↥(aug p Q ^ (m+2))) =
      Module.finrank k (↥(aug p Q ^ (m+1))) := by
  classical
  unfold augCoeffs augLayer
  -- rank-nullity for the quotient by the included next power
  have h := Submodule.finrank_quotient_add_finrank
      ((aug p Q ^ (m+1+1)).comap (aug p Q ^ (m+1)).subtype)
  -- the subspace in a subtype is equivalent to the smaller power itself
  -- using the positive-power inclusion
  have hinc : aug p Q ^ (m+2) ≤ aug p Q ^ (m+1) :=
    pow_antitone_succ p Q m
  let inc : (↥(aug p Q ^ (m+2))) →ₗ[k] (↥(aug p Q ^ (m+1))) :=
  { toFun := fun x => ⟨(x:B), hinc x.property⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have heq : LinearMap.range inc =
        (aug p Q ^ (m+1+1)).comap (aug p Q ^ (m+1)).subtype := by
    -- equality of submodules of the larger subtype
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change ( ( (⟨(y:B), hinc y.property⟩ : (↥(aug p Q ^ (m+1)))) : B)) ∈
        aug p Q ^ (m+1+1)
      simpa [show m+2 = m+1+1 by omega] using y.property
    · intro hx
      change (x : B) ∈ aug p Q ^ (m+1+1) at hx
      have hx' : (x:B) ∈ aug p Q ^ (m+2) := by
        simpa [show m+2 = m+1+1 by omega] using hx
      exact ⟨⟨(x:B), hx'⟩, by rfl⟩
  have hinj : Function.Injective inc := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : (↥(aug p Q ^ (m+1))) => (z:B)) hxy
  have hdiminc : Module.finrank k (↥(LinearMap.range inc)) =
        Module.finrank k (↥(aug p Q ^ (m+2))) := by
    -- rank-nullity, the kernel of the inclusion is zero
    have hr := LinearMap.finrank_range_add_finrank_ker inc
    have hk : LinearMap.ker inc = ⊥ := LinearMap.ker_eq_bot.mpr hinj
    rw [hk] at hr
    simpa using hr
  -- replace the middle dimension in `h`
  have hedim : Module.finrank k
       (↥((aug p Q ^ (m+1+1)).comap (aug p Q ^ (m+1)).subtype)) =
        Module.finrank k (↥(aug p Q ^ (m+2))) := by
    rw [← heq]
    exact hdiminc
  -- the equalities of exponents are purely syntactic in the quotient term
  simpa [show m + 1 + 1 = m + 2 by omega, hedim] using h

/-- The algebraic part of the GS coefficient estimate. The unanswered term is
precisely the drop in the kernels. No cohomology has been used here. -/
lemma coefficient_kernel_drop [Finite Q] (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (m : ℕ) :
    T.card * augCoeffs p Q (m+1) + stepKernelRank p Q T (m+1) =
       augCoeffs p Q (m+2) + stepKernelRank p Q T m := by
  classical
  -- write down the two rank equalities for the successive restricted maps.
  -- Keep the four dimensions opaque; asking `simp_arith!` to normalize the
  -- powers in them eagerly is surprisingly expensive (the definitions include
  -- Finsupps).  `convert` with just the numeral/exponent identities leaves an
  -- entirely Presburger elimination plus the single distributivity of a
  -- numeral multiplier.
  have hm0 := finrank_step p Q T hleft m
  have hs0 := finrank_step p Q T hleft (m+1)
  rw [finrank_freePow p Q T (m+1)] at hm0
  rw [finrank_freePow p Q T (m+2)] at hs0
  have cp0 := coeff_finrank_pow p Q m
  have cq0 := coeff_finrank_pow p Q (m+1)
  have hs : Module.finrank k (↥(aug p Q ^ (m+3))) +
          stepKernelRank p Q T (m+1) =
          T.card * Module.finrank k (↥(aug p Q ^ (m+2))) := by
    -- only the exponents are different from `hs0`.
    simpa only [show m+1+2 = m+3 by omega,
                show m+1+1 = m+2 by omega] using hs0
  have hm : Module.finrank k (↥(aug p Q ^ (m+2))) +
          stepKernelRank p Q T m =
          T.card * Module.finrank k (↥(aug p Q ^ (m+1))) := by
    exact hm0
  have cp : augCoeffs p Q (m+1) +
          Module.finrank k (↥(aug p Q ^ (m+2))) =
          Module.finrank k (↥(aug p Q ^ (m+1))) := cp0
  have cq : augCoeffs p Q (m+2) +
          Module.finrank k (↥(aug p Q ^ (m+3))) =
          Module.finrank k (↥(aug p Q ^ (m+2))) := by
    simpa only [show m+1+1 = m+2 by omega,
                show m+1+2 = m+3 by omega] using cq0
  -- multiplying an additive dimension by the fixed cardinal leaves an
  -- ordinary arithmetic equality; no ring/module definitions are unfolded.
  have hm' : Module.finrank k (↥(aug p Q ^ (m+2))) +
          stepKernelRank p Q T m =
          T.card * augCoeffs p Q (m+1) +
            T.card * Module.finrank k (↥(aug p Q ^ (m+2))) := by
    calc
      _ = T.card * Module.finrank k (↥(aug p Q ^ (m+1))) := hm
      _ = T.card * (augCoeffs p Q (m+1) +
          Module.finrank k (↥(aug p Q ^ (m+2)))) := by rw [cp]
      _ = _ := Nat.mul_add _ _ _
  -- now it is just cancellation in ℕ, without subtraction.
  omega


/-- Forget one power in a tuple of coefficients.  Naming this map is useful:
its restriction to the presentation kernels is the map between successive
kernel filtrations.  Keeping the forgetful map separate prevents Lean from
reducing a large dependently typed term every time the kernel map is used. -/
def freePowInc (T : Finset Q) (m : ℕ) :
    (freePow p Q T (m+2)) →ₗ[k] (freePow p Q T (m+1)) :=
{ toFun := fun x => ⟨(x : relFree p Q T), fun i =>
      pow_antitone_succ p Q m (x.property i)⟩
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl }

@[simp] lemma freePowInc_vec (T : Finset Q) (m : ℕ)
    (x : freePow p Q T (m+2)) :
    (((freePowInc p Q T m) x : freePow p Q T (m+1)) : relFree p Q T)
      = (x : relFree p Q T) := rfl

/-- The forgetful map carries a deeper presentation kernel to the shallower
one.  Both equations are best checked in the ambient group algebra rather
than in the two different subtypes of powers. -/
lemma freePowInc_mem_ker (T : Finset Q) (m : ℕ)
    (x : freePow p Q T (m+2))
    (hx : x ∈ LinearMap.ker (stepMap p Q T (m+1))) :
    (freePowInc p Q T m x) ∈ LinearMap.ker (stepMap p Q T m) := by
  -- extract the equality in `B` once, by the published value lemma for
  -- `stepMap`; unfolding that map under `change` asks the kernel reducer to
  -- compare two enormous subtype expressions.
  have hx' : stepMap p Q T (m+1) x = 0 :=
    (LinearMap.mem_ker).1 hx
  have hz : relMap p Q T (x : relFree p Q T) =
      (0 : MonoidAlgebra (ZMod p) Q) := by
    have h := congrArg
      (fun z : (↥(aug p Q ^ ((m+1)+2))) =>
        (z : MonoidAlgebra (ZMod p) Q)) hx'
    simpa only [stepMap_val, Submodule.coe_zero] using h
  apply (LinearMap.mem_ker).2
  -- Equality of subtypes: after `congrArg`/`stepMap_val` both sides live in
  -- the same ambient group algebra. `freePowInc_vec` then supplies the only
  -- change of tuple involved.
  apply Subtype.ext
  have hval := hz
  -- avoiding `change ...` keeps the two exponents opaque to elaboration.
  simpa only [stepMap_val, freePowInc_vec, Submodule.coe_zero] using hval

/-- Restriction of `freePowInc` to the actual kernels. -/
def kerInclusion (T : Finset Q) (m : ℕ) :
    (LinearMap.ker (stepMap p Q T (m+1))) →ₗ[k]
      (LinearMap.ker (stepMap p Q T m)) :=
  LinearMap.restrict (freePowInc p Q T m)
    (p := LinearMap.ker (stepMap p Q T (m+1)))
    (q := LinearMap.ker (stepMap p Q T m))
    (by
      intro x hx
      exact freePowInc_mem_ker p Q T m x hx)

@[simp] lemma kerInclusion_vec (T : Finset Q) (m : ℕ)
    (x : (LinearMap.ker (stepMap p Q T (m+1)))) :
    ((((kerInclusion p Q T m) x : (LinearMap.ker (stepMap p Q T m)))
        : (freePow p Q T (m+1))) : relFree p Q T)
       = (x.1.1 : relFree p Q T) := rfl

lemma kerInclusion_injective (T : Finset Q) (m : ℕ) :
    Function.Injective (kerInclusion p Q T m) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  have h' := congrArg
     (fun z : (LinearMap.ker (stepMap p Q T m)) =>
        ((z.1 : (freePow p Q T (m+1))) : relFree p Q T)) h
  exact h'

/-- The induced layer of the kernel. It is the last algebraic object before
one brings in minimal relations or `H²`. -/
abbrev kernelLayer (T : Finset Q) (m : ℕ) : Type _ :=
    (LinearMap.ker (stepMap p Q T m)) ⧸
      (LinearMap.range (kerInclusion p Q T m))

lemma finrank_kerInclusion [Finite Q] (T : Finset Q) (m : ℕ) :
    Module.finrank k (↥(LinearMap.range (kerInclusion p Q T m))) =
       stepKernelRank p Q T (m+1) := by
  classical
  have hr := LinearMap.finrank_range_add_finrank_ker
       (kerInclusion p Q T m)
  have hk : LinearMap.ker (kerInclusion p Q T m) = ⊥ :=
      LinearMap.ker_eq_bot.mpr (kerInclusion_injective p Q T m)
  rw [hk] at hr
  simpa [stepKernelRank] using hr

lemma finrank_kernelLayer [Finite Q] (T : Finset Q) (m : ℕ) :
    Module.finrank k (kernelLayer p Q T m) +
       stepKernelRank p Q T (m+1) = stepKernelRank p Q T m := by
  classical
  have h := Submodule.finrank_quotient_add_finrank
       (LinearMap.range (kerInclusion p Q T m))
  have h' := finrank_kerInclusion p Q T m
  simpa [kernelLayer, stepKernelRank, h'] using h

/-- A convenient numerical eliminator: a bound on the intervening kernel
layer is exactly the bound on the drop of kernel ranks. -/
lemma kernel_drop_of_layer [Finite Q] (T : Finset Q) (m c : ℕ)
    (h : Module.finrank k (kernelLayer p Q T m) ≤ c) :
    stepKernelRank p Q T m ≤ stepKernelRank p Q T (m+1) + c := by
  have e := finrank_kernelLayer p Q T m
  omega

end GSsupport

namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- If a positive coefficient vanishes, the power under it is already zero.
This is the useful one-sided form of Nakayama for the filtration. It is
important to record it at the level of powers, not just coefficients: the
kernels in the presentation are kernels *inside* these powers. -/
lemma pow_eq_bot_of_coeff_zero [Finite Q] (hp : IsPGroup p Q)
    (n : ℕ) (hn : 0 < n) (hz : augCoeffs p Q n = 0) :
    aug p Q ^ n = (⊥ : Submodule k B) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  -- Equality of dimensions of two consecutive powers is equality of the
  -- powers, because the smaller one is included in the larger one.
  have c := coeff_finrank_pow p Q m
  have eqdim : Module.finrank k (↥(aug p Q ^ (m+1+1))) =
      Module.finrank k (↥(aug p Q ^ (m+1))) := by
    -- `c` is written with `m+2`.
    simpa [show m+1+1 = m+2 by omega, hz] using c
  have eqpow : aug p Q ^ (m+2) = aug p Q ^ (m+1) := by
    have le := pow_antitone_succ p Q m
    apply Submodule.eq_of_le_of_finrank_eq le
    simpa [show m+1+1 = m+2 by omega] using eqdim
  by_contra h
  exact (aug_power_strict p Q hp m h) eqpow

/-- When the domain power of a step is zero its kernel is zero. Keeping this
lemma separate from the coefficient lemma above makes the zero-coefficient
case of the missing `H²` comparison completely algebraic; no relation
information is needed at terminal layers. -/
lemma stepKernelRank_eq_zero_of_pow [Finite Q] (T : Finset Q) (m : ℕ)
    (hpw : aug p Q ^ (m+1) = (⊥ : Submodule k B)) :
    stepKernelRank p Q T m = 0 := by
  classical
  -- Every tuple in the domain has all its entries in the zero submodule.
  have allzero (x : freePow p Q T (m+1)) : x = 0 := by
    apply Subtype.ext
    funext i
    have hi : (x.1 i : B) ∈ aug p Q ^ (m+1) := x.2 i
    rw [hpw] at hi
    -- membership of the bottom submodule is equality with zero
    simpa using hi
  letI : Subsingleton (freePow p Q T (m+1)) :=
    ⟨fun a b => (allzero a).trans (allzero b).symm⟩
  letI : Subsingleton (↥(LinearMap.ker (stepMap p Q T m))) :=
    ⟨by
      intro a b
      apply Subtype.ext
      exact Subsingleton.elim _ _⟩
  unfold stepKernelRank
  exact Module.finrank_zero_of_subsingleton

/-- The layer inequality has no obstruction at indices whose coefficient is
zero. This isolates the honest (positive-coefficient) degree-two comparison;
one does not need an `H²` theorem for the terminal zero layers. -/
lemma finrank_kernelLayer_eq_zero_of_coeff_zero [Finite Q]
    (hp : IsPGroup p Q) (T : Finset Q) (m : ℕ)
    (hz : augCoeffs p Q m = 0) :
    Module.finrank k (kernelLayer p Q T m) = 0 := by
  classical
  have hm : 0 < m := by
    -- the zeroth coefficient is `1`
    apply Nat.pos_of_ne_zero
    intro h
    subst m
    have h0 := augCoeffs_zero p Q
    omega
  have pbot : aug p Q ^ m = (⊥ : Submodule k B) :=
    pow_eq_bot_of_coeff_zero p Q hp m hm hz
  -- the domain of `stepMap m` uses `m+1`; this is the same zero power,
  -- since a product with a zero power is zero. We only need inclusion.
  have inc : aug p Q ^ (m+1) ≤ aug p Q ^ m := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    simpa [show i+1+1 = i+2 by omega] using (pow_antitone_succ p Q i)
  have pbot' : aug p Q ^ (m+1) = (⊥ : Submodule k B) :=
    bot_unique (by
      intro x hx
      have hx' : x ∈ aug p Q ^ m := inc hx
      rw [pbot] at hx'
      exact hx')
  have hk : stepKernelRank p Q T m = 0 :=
    stepKernelRank_eq_zero_of_pow p Q T m pbot'
  have layer := finrank_kernelLayer p Q T m
  omega

end GSsupport

namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p

/-- Even without second-degree information the layer of kernels is no larger
than the whole next free layer. In this form the assertion is about
*coefficients*, not total dimensions of powers; cancellation of the two
rank identities above is what makes it useful. -/
lemma finrank_kernelLayer_le_freeCoefficient [Finite Q]
    (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T) (m : ℕ) :
    Module.finrank k (kernelLayer p Q T m) ≤
       T.card * augCoeffs p Q (m+1) := by
  classical
  have ker := finrank_kernelLayer p Q T m
  have c := coefficient_kernel_drop p Q T hleft m
  omega
end GSsupport

namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p

/-- In a one-column augmentation presentation the restricted kernel has
exactly the size of the source coefficient.  This is a useful degenerate
case of the translated-layer comparison: it uses only rank-nullity for the
onto step, no minimal relations at all. -/
lemma stepKernelRank_eq_coeff_of_card_one [Finite Q]
    (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (hc : T.card = 1) (m : ℕ) :
    stepKernelRank p Q T m = augCoeffs p Q (m+1) := by
  classical
  have st := finrank_step p Q T hleft m
  have co := coeff_finrank_pow p Q m
  -- with a single column the two right hand sides are the same power
  rw [finrank_freePow p Q T (m+1), hc] at st
  -- `simp` only removes the multiplier `1`
  simp only [one_mul] at st
  omega

/-- Consequently the positive Hilbert coefficients in a one-column
presentation cannot increase.  The embedded step kernels form a descending
chain, and in this case each of them is the corresponding coefficient. -/
lemma coeff_succ_le_of_card_one [Finite Q]
    (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (hc : T.card = 1) (m : ℕ) (hm : 0 < m) :
    augCoeffs p Q (m+1) ≤ augCoeffs p Q m := by
  classical
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have kl := finrank_kernelLayer p Q T i
  have s0 := stepKernelRank_eq_coeff_of_card_one p Q T hleft hc i
  have s1 := stepKernelRank_eq_coeff_of_card_one p Q T hleft hc (i+1)
  have s1' : stepKernelRank p Q T (i+1) =
        augCoeffs p Q (i+2) := by
    simpa only [show i+1+1 = i+2 by omega] using s1
  -- normalize the two indices of the goal as well. `omega` does not
  -- rewrite an application of `augCoeffs` at propositionally equal indices.
  change augCoeffs p Q (i+2) ≤ augCoeffs p Q (i+1)
  -- the layer dimension witnesses monotonicity of the two consecutive
  -- restricted kernels; replace them by the displayed coefficients
  omega
end GSsupport

namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p

/-- The layer, not just the difference of kernel ranks, has an exact
coefficient formula.  It is helpful before any relation comparison: in this
small presentation the source and target of the associated-graded arrow are
`T` copies of the next coefficient and the following coefficient
respectively, and the arrow is already onto. -/
lemma finrank_kernelLayer_add_coeff [Finite Q]
    (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T) (m : ℕ) :
    Module.finrank k (kernelLayer p Q T m) + augCoeffs p Q (m+2) =
        T.card * augCoeffs p Q (m+1) := by
  classical
  have kl := finrank_kernelLayer p Q T m
  have cd := coefficient_kernel_drop p Q T hleft m
  omega
end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Filtration.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Relations.lean
section
noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- The (unfiltered) second syzygy in the very small algebra resolution
`B^T -> B -> k`.  We keep it as a submodule over the ground field; multiplication
on the left below is the extra `B`-action. -/
abbrev relSub (T : Finset Q) : Submodule k (relFree p Q T) :=
  LinearMap.ker (relMap p Q T)

/-- The subspace `J R` of the relation module. We take a span of the elementary
products; this has the advantage that no instance asserting a `B`-module
structure on the tuple type is needed. -/
def augRel (T : Finset Q) : Submodule k (relFree p Q T) :=
  Submodule.span k {x | ∃ a : B, a ∈ aug p Q ∧
      ∃ u : relFree p Q T, u ∈ relSub p Q T ∧ x = vecMul p Q T a u}

lemma augRel_le_relSub (T : Finset Q) : augRel p Q T ≤ relSub p Q T := by
  classical
  apply Submodule.span_le.2
  intro x hx
  obtain ⟨a, ha, u, hu, rfl⟩ := hx
  -- the kernel is stable under multiplication on the left
  change relMap p Q T (vecMul p Q T a u) = 0
  simpa [relMap_mul] using
    (show a * relMap p Q T u = (0 : B) by
      rw [show relMap p Q T u = 0 from (LinearMap.mem_ker.1 hu)]; simp)

/-- The top of the relation module, `R / J R`. This is the completely
algebraic avatar of the number of minimal relations. -/
abbrev minimalRel (T : Finset Q) : Type _ :=
  (relSub p Q T) ⧸ (augRel p Q T).comap (relSub p Q T).subtype

/-- Multiplying a vector whose entries are in `J^s` by an element of `J^r`
raises every entry to `J^(r+s)`. We only need the first nontrivial case in the
comparison `JR ⊂ R ∩ J²F`. -/
lemma vecMul_aug_mem_sq (T : Finset Q) (a : B) (ha : a ∈ aug p Q)
    (u : relFree p Q T) (hu : ∀ i, u i ∈ aug p Q) :
    ∀ i, vecMul p Q T a u i ∈ aug p Q ^ 2 := by
  intro i
  -- powers on submodules are `Submodule.mul`
  simpa [pow_two, vecMul] using (Submodule.mul_mem_mul ha (hu i))

/-- In a minimal presentation the augmentation multiples of relations lie in
one further power of every coordinate. This is the little strictness statement
which is enough in degree zero. -/
lemma augRel_coordinates_sq [Finite Q] (T : Finset Q)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    augRel p Q T ≤ freePow p Q T 2 := by
  classical
  apply Submodule.span_le.2
  intro x hx
  obtain ⟨a, ha, u, hu, rfl⟩ := hx
  have hc : ∀ i, u i ∈ aug p Q :=
    relKernel_coordinates p Q T hcard hspan u (LinearMap.mem_ker.1 hu)
  exact vecMul_aug_mem_sq p Q T a ha u hc

/-- At the first interesting index the associated layer of the kernel is a
quotient of the top `R / J R`. This is often the starting point for the
identification of minimal relations with `H²`. All powers and kernels here are
the concrete ones from `Filtration`; no cohomological input is hidden in this
lemma. -/
lemma finrank_kernelLayer_zero_le_minimal [Finite Q] (T : Finset Q)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    Module.finrank k (kernelLayer p Q T 0) ≤
      Module.finrank k (minimalRel p Q T) := by
  classical
  -- Describe maps from `R` into the shallow step-kernel. Minimality says
  -- every relation has entries in `J`, so restriction is legitimate.
  let incR : (relSub p Q T) →ₗ[k]
      (LinearMap.ker (stepMap p Q T 0)) :=
    { toFun := fun u =>
        ⟨⟨(u.1 : relFree p Q T),
            by
              intro i
              -- the first power is `J`
              simpa using
                (relKernel_coordinates p Q T hcard hspan u.1
                  (LinearMap.mem_ker.1 u.2) i)⟩,
          by
            apply (LinearMap.mem_ker).2
            apply Subtype.ext
            -- the equality has already been checked in the ambient relation
            -- module; `stepMap_val` avoids reducing the subtypes
            have hz : relMap p Q T (u.1 : relFree p Q T) = (0 : B) :=
              LinearMap.mem_ker.1 u.2
            simpa only [stepMap_val, Submodule.coe_zero] using hz ⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have incR_surj : Function.Surjective incR := by
    intro z
    -- forgetting the `J` membership of a shallow kernel element is a
    -- relation; there is no choice of lift here.
    let u : relFree p Q T := (z.1.1 : relFree p Q T)
    have hz' : relMap p Q T u = (0 : B) := by
      have h := LinearMap.mem_ker.1 z.2
      have hh := congrArg (fun w : (↥(aug p Q ^ (0+2))) => (w:B)) h
      simpa only [stepMap_val, Submodule.coe_zero] using hh
    let r : relSub p Q T := ⟨u, (LinearMap.mem_ker).2 hz'⟩
    refine ⟨r, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  -- `JR` is killed by the map to the quotient of the shallow kernel by the
  -- deeper one. An element with entries in `J²` and zero `relMap` is exactly a
  -- member of the deeper kernel.
  let out : (relSub p Q T) →ₗ[k] (kernelLayer p Q T 0) :=
      (Submodule.mkQ _).comp incR
  have kill : (augRel p Q T).comap (relSub p Q T).subtype ≤
      LinearMap.ker out := by
    intro x hx
    -- first lift the square-coordinate vector to the deeper step kernel
    have xsq : (x.1 : relFree p Q T) ∈ freePow p Q T 2 :=
      augRel_coordinates_sq p Q T hcard hspan hx
    let y : freePow p Q T 2 := ⟨x.1, xsq⟩
    have hyz : relMap p Q T (y : relFree p Q T) = (0:B) :=
      LinearMap.mem_ker.1 x.2
    have hyker : y ∈ LinearMap.ker (stepMap p Q T (0+1)) := by
      apply (LinearMap.mem_ker).2
      apply Subtype.ext
      simpa only [stepMap_val, Submodule.coe_zero] using hyz
    let yy : (LinearMap.ker (stepMap p Q T (0+1))) := ⟨y, hyker⟩
    have heq : incR x = kerInclusion p Q T 0 yy := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    apply (LinearMap.mem_ker).2
    -- a vector in the range of the deeper kernel dies in the quotient
    change (Submodule.mkQ (LinearMap.range (kerInclusion p Q T 0)))
        (incR x) = 0
    rw [heq]
    -- `mkQ` kills its submodule
    exact (Submodule.Quotient.mk_eq_zero _).2
      (show (kerInclusion p Q T 0 yy) ∈
        LinearMap.range (kerInclusion p Q T 0) from
          ⟨yy, rfl⟩)
  let f : minimalRel p Q T →ₗ[k] (kernelLayer p Q T 0) :=
      Submodule.liftQ _ out kill
  have fsurj : Function.Surjective f := by
    intro z
    -- `mkQ` from the shallow kernel is onto and `incR` is onto it.
    obtain ⟨w, rfl⟩ := (Submodule.mkQ_surjective
       (LinearMap.range (kerInclusion p Q T 0))) z
    obtain ⟨r, hr⟩ := incR_surj w
    refine ⟨(Submodule.mkQ _ r), ?_⟩
    change Submodule.mkQ _ (incR r) = _
    rw [hr]
  exact LinearMap.finrank_le_finrank_of_surjective fsurj

end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Relations.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/NakayamaRel.lean
section

noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- The honest `J^n R` span.  Keeping it as a subspace over the residue
field avoids a second module structure on tuples. -/
def powerRel (T : Finset Q) (n : ℕ) : Submodule k (relFree p Q T) :=
  Submodule.span k {x | ∃ a : B, a ∈ aug p Q ^ n ∧
      ∃ u : relFree p Q T, u ∈ relSub p Q T ∧
        x = vecMul p Q T a u}

lemma relSub_mem_powerRel_zero (T : Finset Q)
    (u : relFree p Q T) (hu : u ∈ relSub p Q T) :
    u ∈ powerRel p Q T 0 := by
  classical
  apply Submodule.subset_span
  refine ⟨(1:B), ?_, u, hu, ?_⟩
  · refine ⟨1, ?_⟩
    simp
  · funext i
    simp [vecMul]

/-- Multiplication on the left by an element of `J` raises the honest
`J^n R` span by one.  This is proved by span induction because our tuples
were deliberately only made modules over the ground field. -/
lemma vecMul_powerRel_succ (T : Finset Q) (n : ℕ)
    (b : B) (hb : b ∈ aug p Q)
    (x : relFree p Q T) (hx : x ∈ powerRel p Q T n) :
    vecMul p Q T b x ∈ powerRel p Q T (n+1) := by
  classical
  -- induction in the coefficient-field span describing `J^n R`
  refine Submodule.span_induction (p := fun x (_ : x ∈
      Submodule.span k {x : relFree p Q T |
        ∃ a : B, a ∈ aug p Q ^ n ∧
          ∃ u : relFree p Q T, u ∈ relSub p Q T ∧
            x = vecMul p Q T a u}) =>
      vecMul p Q T b x ∈ powerRel p Q T (n+1)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨a, ha, u, hu, rfl⟩
    -- `J * J^n = J^(n+1)` for submodule multiplication
    have hba : b * a ∈ aug p Q ^ (n+1) := by
      have h' : b * a ∈ aug p Q * (aug p Q ^ n) :=
        Submodule.mul_mem_mul hb ha
      -- the same version of `pow_succ` is convenient here
      simpa [pow_succ'] using h'
    rw [vecMul_assoc]
    apply Submodule.subset_span
    exact ⟨b*a, hba, u, hu, rfl⟩
  · -- zero tuple
    have hz : vecMul p Q T b (0 : relFree p Q T) = 0 := by
      funext i
      simp [vecMul]
    rw [hz]
    exact (powerRel p Q T (n+1)).zero_mem
  · intro x y hx hy ix iy
    rw [vecMul_add']
    exact (powerRel p Q T (n+1)).add_mem ix iy
  · intro c x hx ix
    -- left multiplication is linear over the central coefficient field
    have he : vecMul p Q T b (c • x) =
        c • vecMul p Q T b x := by
      funext i
      simp [vecMul, mul_smul_comm]
    rw [he]
    exact (powerRel p Q T (n+1)).smul_mem c ix

/-- If every relation is an augmentation multiple of relations, then every
relation is in every power `J^n R`. This small Nakayama iteration is useful
also for positive coefficient layers: it removes the apparent zero-generator
exception without any cohomology input. -/
lemma relSub_mem_powerRel_all (T : Finset Q)
    (hJR : ∀ u : relFree p Q T, u ∈ relSub p Q T → u ∈ augRel p Q T) :
    ∀ n : ℕ, ∀ u : relFree p Q T, u ∈ relSub p Q T →
      u ∈ powerRel p Q T n := by
  classical
  intro n
  induction n with
  | zero =>
      intro u hu
      exact relSub_mem_powerRel_zero p Q T u hu
  | succ n ih =>
      intro u hu
      have hs : u ∈ augRel p Q T := hJR u hu
      -- now expand a spanning expression for `u ∈ J R`
      refine Submodule.span_induction (p := fun x (_ : x ∈
          Submodule.span k {x : relFree p Q T |
            ∃ a : B, a ∈ aug p Q ∧
              ∃ v : relFree p Q T, v ∈ relSub p Q T ∧
                x = vecMul p Q T a v}) =>
          x ∈ powerRel p Q T (n+1)) ?_ ?_ ?_ ?_ hs
      · intro x hx
        rcases hx with ⟨b, hb, v, hv, rfl⟩
        exact vecMul_powerRel_succ p Q T n b hb v (ih v hv)
      · exact (powerRel p Q T (n+1)).zero_mem
      · intro x y hx hy ix iy
        exact (powerRel p Q T (n+1)).add_mem ix iy
      · intro c x hx ix
        exact (powerRel p Q T (n+1)).smul_mem c ix

/-- At a nilpotent augmentation ideal, a residue-zero module has no
relations at all.  This is the elementary Nakayama argument but made with
our field-spans `augRel`, so it can be used without any `B`-module instance on
function-tuples. -/
lemma relSub_eq_bot_of_quotient_zero [Finite Q]
    (hp : IsPGroup p Q) (T : Finset Q)
    (hz : Module.finrank k (minimalRel p Q T) = 0) :
    relSub p Q T = ⊥ := by
  classical
  -- a zero quotient says precisely that every relation already lies in JR
  letI : Subsingleton (minimalRel p Q T) :=
    (Module.finrank_zero_iff).1 hz
  have hJR : ∀ u : relFree p Q T,
      u ∈ relSub p Q T → u ∈ augRel p Q T := by
    intro u hu
    let ru : relSub p Q T := ⟨u, hu⟩
    have hzero : (Submodule.Quotient.mk ru : minimalRel p Q T) = 0 :=
      Subsingleton.elim _ _
    have hc : ru ∈ (augRel p Q T).comap (relSub p Q T).subtype :=
      (Submodule.Quotient.mk_eq_zero
        ((augRel p Q T).comap (relSub p Q T).subtype)).1 hzero
    exact hc
  obtain ⟨N, hN⟩ := aug_nilpotent p Q hp
  -- the `N`th power span is zero
  have hpow : powerRel p Q T N = (⊥ : Submodule k (relFree p Q T)) := by
    apply le_antisymm
    · apply Submodule.span_le.2
      intro x hx
      rcases hx with ⟨a, ha, u, hu, rfl⟩
      -- membership in the bottom power forces the coefficient to be zero
      have ha0 : a = (0:B) := by
        rw [hN] at ha
        simpa using ha
      subst a
      -- pointwise zero tuple
      change vecMul p Q T (0:B) u ∈ (⊥ : Submodule k (relFree p Q T))
      change vecMul p Q T (0:B) u = 0
      funext i
      simp [vecMul]
    · exact bot_le
  apply le_antisymm
  · intro u hu
    have hu' : u ∈ powerRel p Q T N :=
      relSub_mem_powerRel_all p Q T hJR N u hu
    rw [hpow] at hu'
    exact hu'
  · exact bot_le

/-- Consequently every translated kernel layer is zero in the residue-zero
case. This isolates a genuine positive-relation obstruction in the hard
branch of the GS estimate. -/
lemma finrank_kernelLayer_zero_of_minimal_zero [Finite Q]
    (hp : IsPGroup p Q) (T : Finset Q) (m : ℕ)
    (hz : Module.finrank k (minimalRel p Q T) = 0) :
    Module.finrank k (kernelLayer p Q T m) = 0 := by
  classical
  have hR := relSub_eq_bot_of_quotient_zero p Q hp T hz
  -- the restricted step-kernel has no nonzero vector, since its underlying
  -- tuple is a relation.
  have allzero (x : LinearMap.ker (stepMap p Q T m)) : x = 0 := by
    have hh : relMap p Q T (x.1 : relFree p Q T) = (0:B) := by
      have h := LinearMap.mem_ker.1 x.2
      have h' := congrArg (fun w : (↥(aug p Q ^ (m+2))) => (w:B)) h
      simpa only [stepMap_val, Submodule.coe_zero] using h'
    have hxR : (x.1 : relFree p Q T) ∈ relSub p Q T :=
      (LinearMap.mem_ker).2 hh
    rw [hR] at hxR
    have hvec : (x.1 : relFree p Q T) = 0 := by
      simpa using hxR
    apply Subtype.ext
    apply Subtype.ext
    exact hvec
  letI : Subsingleton (LinearMap.ker (stepMap p Q T m)) :=
    ⟨fun a b => (allzero a).trans (allzero b).symm⟩
  -- a quotient of a singleton is a singleton
  letI : Subsingleton (kernelLayer p Q T m) :=
    ⟨by
      intro a b
      -- all representatives have the same value; quotient induction is
      -- the cleanest way to avoid normal forms for `Submodule.mkQ`
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
        (LinearMap.range (kerInclusion p Q T m)) a
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
        (LinearMap.range (kerInclusion p Q T m)) b
      have he : x = y := Subsingleton.elim _ _
      rw [he]⟩
  exact Module.finrank_zero_of_subsingleton

end GSsupport

namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- Forgetting the coefficient power maps a restricted kernel injectively to
an ordinary relation.  It is a handy coarse estimate before invoking any
filtered relation comparison. -/
def stepKerToRel (T : Finset Q) (m : ℕ) :
    (LinearMap.ker (stepMap p Q T m)) →ₗ[k] (relSub p Q T) :=
  { toFun := fun x =>
      ⟨(x.1 : relFree p Q T), by
        apply (LinearMap.mem_ker).2
        have h := LinearMap.mem_ker.1 x.2
        have h' := congrArg (fun w : (↥(aug p Q ^ (m+2))) => (w:B)) h
        simpa only [stepMap_val, Submodule.coe_zero] using h'⟩
    map_add' := by intro a b; rfl
    map_smul' := by intro a b; rfl }

lemma stepKerToRel_injective (T : Finset Q) (m : ℕ) :
    Function.Injective (stepKerToRel p Q T m) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z : relSub p Q T => (z.1 : relFree p Q T)) h

/-- Every translated quotient is, coarsely, no larger than the entire
relation subspace.  Later estimates replace this total dimension by the
correct single coefficient of its associated graded; this statement needs no
strictness. -/
lemma finrank_kernelLayer_le_relSub [Finite Q]
    (T : Finset Q) (m : ℕ) :
    Module.finrank k (kernelLayer p Q T m) ≤
      Module.finrank k (relSub p Q T) := by
  classical
  -- quotient by a subspace never increases dimension
  have hq := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (kerInclusion p Q T m))
  have hq' : Module.finrank k (kernelLayer p Q T m) ≤
      Module.finrank k (LinearMap.ker (stepMap p Q T m)) := by
    exact Nat.le.intro hq
  have hi := LinearMap.finrank_le_finrank_of_injective
    (f := stepKerToRel p Q T m) (stepKerToRel_injective p Q T m)
  exact hq'.trans hi

end GSsupport

namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

lemma finrank_algebra_eq_card [Finite Q] :
    Module.finrank k B = Nat.card Q := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  calc
    Module.finrank k B = Module.finrank k (Q → k) :=
      LinearEquiv.finrank_eq (Finsupp.linearEquivFunOnFinite k k Q)
    _ = Fintype.card Q := Module.finrank_fintype_fun_eq_card k
    _ = Nat.card Q := by exact (Nat.card_eq_fintype_card).symm

lemma eps_surjective : Function.Surjective (eps p Q) := by
  intro c
  refine ⟨c • (1:B), ?_⟩
  simp

lemma finrank_aug_add_one [Finite Q] :
    1 + Module.finrank k (↥(aug p Q)) = Nat.card Q := by
  classical
  have h := LinearMap.finrank_range_add_finrank_ker (eps p Q).toLinearMap
  have ht : LinearMap.range (eps p Q).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (eps_surjective p Q)
  -- the kernel is definitionally `aug`
  have hb := finrank_algebra_eq_card p Q
  rw [ht] at h
  change 1 + Module.finrank k (↥(LinearMap.ker (eps p Q).toLinearMap)) = Nat.card Q
  simpa [hb] using h

lemma finrank_relFree_eq [Finite Q]
    (T : Finset Q) :
    Module.finrank k (relFree p Q T) = T.card * Nat.card Q := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  -- a tuple of finitely many group algebra elements
  have hb : Module.finrank k B = Nat.card Q :=
    finrank_algebra_eq_card p Q
  -- use the finite dependent-product formula, then the constant summand
  calc
    Module.finrank k (relFree p Q T) =
        ∑ _i : (↥T), Module.finrank k B :=
          Module.finrank_pi_fintype k
    _ = T.card * Nat.card Q := by simp [hb]

/-- Total size of the relation kernel.  This is often a useful cheap
comparison on translated layers before their associated-graded estimate.
It follows just from onto-`J` of the first arrow. -/
lemma finrank_relSub_add [Finite Q]
    (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T) :
    Module.finrank k (↥(aug p Q)) +
       Module.finrank k (↥(relSub p Q T)) = T.card * Nat.card Q := by
  classical
  have hr := LinearMap.finrank_range_add_finrank_ker (relMap p Q T)
  have heq : LinearMap.range (relMap p Q T) = aug p Q := by
    apply le_antisymm
    · rintro x ⟨u, rfl⟩
      exact relMap_mem_aug p Q T u
    · -- its range is the generated left ideal
      rw [relMap_range]
      exact hleft
  rw [heq] at hr
  simpa [relSub, finrank_relFree_eq p Q T] using hr

end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/NakayamaRel.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/RelCocycle.lean
section
noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- A functional on the top of the relation module, regarded as a functional
on honest relations. -/
def minFunc (T : Finset Q)
    (l : Module.Dual k (minimalRel p Q T)) :
    (relSub p Q T) →ₗ[k] k := l.comp (Submodule.mkQ _)

lemma minFunc_aug (T : Finset Q)
    (l : Module.Dual k (minimalRel p Q T))
    (x : relSub p Q T)
    (hx : (x.1 : relFree p Q T) ∈ augRel p Q T) :
    minFunc p Q T l x = 0 := by
  unfold minFunc
  have hmem : x ∈ (augRel p Q T).comap (relSub p Q T).subtype := hx
  have hz : (Submodule.mkQ ((augRel p Q T).comap (relSub p Q T).subtype)) x = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hmem
  change l ((Submodule.mkQ _) x) = 0
  rw [hz, map_zero]

/-- The quotient functional is invariant for the left `B` action: on `k` the
 action is the augmentation. This elementary lemma is the reason the
 two-bars give ordinary (trivial coefficient) cocycles. -/
lemma minFunc_mul (T : Finset Q)
    (l : Module.Dual k (minimalRel p Q T))
    (a : B) (u : relFree p Q T) (hu : u ∈ relSub p Q T) :
    minFunc p Q T l
       (⟨vecMul p Q T a u,
          by
            apply (LinearMap.mem_ker).2
            rw [relMap_mul, LinearMap.mem_ker.1 hu, mul_zero]⟩ : relSub p Q T) =
      (eps p Q a) * minFunc p Q T l ⟨u,hu⟩ := by
  classical
  let a0 : B := a - (eps p Q a) • (1:B)
  have ha0 : a0 ∈ aug p Q := by
    change eps p Q (a - (eps p Q a) • (1:B)) = 0
    simp
  let uu : relSub p Q T := ⟨u, hu⟩
  let ja : relFree p Q T := vecMul p Q T a0 u
  have hjarel : ja ∈ relSub p Q T := by
    apply (LinearMap.mem_ker).2
    rw [show ja = vecMul p Q T a0 u by rfl, relMap_mul,
      LinearMap.mem_ker.1 hu, mul_zero]
  have hja_aug : ja ∈ augRel p Q T := by
    apply Submodule.subset_span
    exact ⟨a0, ha0, u, hu, rfl⟩
  have hz : minFunc p Q T l (⟨ja, hjarel⟩ : relSub p Q T) = 0 :=
    minFunc_aug p Q T l _ hja_aug
  -- split `a` into its scalar part and augmentation part; all equalities of
  -- tuples are pointwise ring calculations.
  have hadec : a = a0 + (eps p Q a) • (1:B) := by
    dsimp [a0]
    abel
  have hvdec : vecMul p Q T a u = ja + (eps p Q a) • u := by
    funext i
    change a * u i = a0 * u i + (eps p Q a) • u i
    conv_lhs => rw [hadec]
    simp [add_mul]

  let leftr : relSub p Q T :=
    ⟨vecMul p Q T a u,
      by
        apply (LinearMap.mem_ker).2
        rw [relMap_mul, LinearMap.mem_ker.1 hu, mul_zero]⟩
  have heq : leftr = (⟨ja, hjarel⟩ : relSub p Q T) +
        (eps p Q a) • uu := by
    apply Subtype.ext
    exact hvdec
  change minFunc p Q T l leftr = _
  rw [heq, map_add, hz, zero_add, map_smul]
  rfl

/-- The bar identity prior to applying an invariant functional. It uses no
normalization of the chosen section. -/
lemma bar_assoc (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (q r s : Q) :
    barRelation p Q T hleft q r +
        barRelation p Q T hleft (q*r) s =
      barRelation p Q T hleft q (r*s) +
        vecMul p Q T (MonoidAlgebra.of k Q q)
          (barRelation p Q T hleft r s) := by
  classical
  -- this is the cancellation in the ordinary bar complex
  unfold barRelation
  funext i
  -- all vector operations are pointwise; remove the names of the chosen
  -- lifts and use only associativity and `[q][r]=[qr]`.
  change
    (genLiftVec p Q T hleft q i +
      (MonoidAlgebra.of k Q q : B) * genLiftVec p Q T hleft r i -
        genLiftVec p Q T hleft (q*r) i) +
      (genLiftVec p Q T hleft (q*r) i +
        (MonoidAlgebra.of k Q (q*r) : B) * genLiftVec p Q T hleft s i -
          genLiftVec p Q T hleft ((q*r)*s) i) =
    (genLiftVec p Q T hleft q i +
        (MonoidAlgebra.of k Q q : B) * genLiftVec p Q T hleft (r*s) i -
          genLiftVec p Q T hleft (q*(r*s)) i) +
      (MonoidAlgebra.of k Q q : B) *
        (genLiftVec p Q T hleft r i +
          (MonoidAlgebra.of k Q r : B) * genLiftVec p Q T hleft s i -
            genLiftVec p Q T hleft (r*s) i)
  rw [map_mul]
  -- keeping the product non-commutative, distributivity and associativity are
  -- enough.
  simp only [mul_add, mul_sub, mul_assoc]
  -- normalize the group-product argument of the arbitrary section
  noncomm_ring

/-- The value of a top relation functional on a two-bar. -/
def relCocycle (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (l : Module.Dual k (minimalRel p Q T)) (q r : Q) : k :=
  minFunc p Q T l
    (⟨barRelation p Q T hleft q r,
      (LinearMap.mem_ker).2 (relMap_barRelation p Q T hleft q r)⟩ : relSub p Q T)

/-- The coefficients above satisfy the inhomogeneous two-cocycle equation for
trivial coefficients. -/
lemma relCocycle_condition (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T)
    (l : Module.Dual k (minimalRel p Q T)) (q r s : Q) :
    relCocycle p Q T hleft l q r + relCocycle p Q T hleft l (q*r) s =
       relCocycle p Q T hleft l q (r*s) + relCocycle p Q T hleft l r s := by
  classical
  -- apply the invariant functional to `bar_assoc`
  have he := bar_assoc p Q T hleft q r s
  have hv : minFunc p Q T l
        (⟨vecMul p Q T (MonoidAlgebra.of k Q q)
             (barRelation p Q T hleft r s),
          by
            apply (LinearMap.mem_ker).2
            rw [relMap_mul, relMap_barRelation, mul_zero]⟩ : relSub p Q T) =
        minFunc p Q T l
          (⟨barRelation p Q T hleft r s,
             (LinearMap.mem_ker).2
               (relMap_barRelation p Q T hleft r s)⟩ : relSub p Q T) := by
      have h := minFunc_mul p Q T l
          (MonoidAlgebra.of k Q q : B)
          (barRelation p Q T hleft r s)
          ((LinearMap.mem_ker).2 (relMap_barRelation p Q T hleft r s))
      convert h using 1 <;> try { rw [eps_of]; simp }

  -- coerce equality of tuples to equality in `relSub`, then apply linearity
  have he' :
      (⟨barRelation p Q T hleft q r,
          (LinearMap.mem_ker).2
            (relMap_barRelation p Q T hleft q r)⟩ : relSub p Q T) +
        ⟨barRelation p Q T hleft (q*r) s,
          (LinearMap.mem_ker).2
            (relMap_barRelation p Q T hleft (q*r) s)⟩ =
      (⟨barRelation p Q T hleft q (r*s),
          (LinearMap.mem_ker).2
            (relMap_barRelation p Q T hleft q (r*s))⟩ : relSub p Q T) +
        ⟨vecMul p Q T (MonoidAlgebra.of k Q q)
             (barRelation p Q T hleft r s), by
             apply (LinearMap.mem_ker).2
             rw [relMap_mul, relMap_barRelation, mul_zero]⟩ := by
    apply Subtype.ext
    exact he
  have hn := congrArg (fun z : relSub p Q T => minFunc p Q T l z) he'
  -- keep the four terms named to make the subtype additions visible
  let A : relSub p Q T :=
    ⟨barRelation p Q T hleft q r,
      (LinearMap.mem_ker).2 (relMap_barRelation p Q T hleft q r)⟩
  let B' : relSub p Q T :=
    ⟨barRelation p Q T hleft (q*r) s,
      (LinearMap.mem_ker).2 (relMap_barRelation p Q T hleft (q*r) s)⟩
  let C' : relSub p Q T :=
    ⟨barRelation p Q T hleft q (r*s),
      (LinearMap.mem_ker).2 (relMap_barRelation p Q T hleft q (r*s))⟩
  let D' : relSub p Q T :=
    ⟨vecMul p Q T (MonoidAlgebra.of k Q q)
             (barRelation p Q T hleft r s), by
             apply (LinearMap.mem_ker).2
             rw [relMap_mul, relMap_barRelation, mul_zero]⟩
  have hn' : minFunc p Q T l (A + B') =
       minFunc p Q T l (C' + D') := by
    exact hn
  rw [map_add, map_add] at hn'
  change _ + _ = _ + _
  -- values on the first three bars are the stated cocycle values
  change minFunc p Q T l A + minFunc p Q T l B' =
      minFunc p Q T l C' +
        minFunc p Q T l
          (⟨barRelation p Q T hleft r s,
             (LinearMap.mem_ker).2
               (relMap_barRelation p Q T hleft r s)⟩ : relSub p Q T)
  have hv' : minFunc p Q T l D' =
        minFunc p Q T l
          (⟨barRelation p Q T hleft r s,
             (LinearMap.mem_ker).2
               (relMap_barRelation p Q T hleft r s)⟩ : relSub p Q T) := hv
  rw [hv'] at hn'
  exact hn'


end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/RelCocycle.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/HomogeneousBridge.lean
section
open CategoryTheory Functor ContinuousMap
open ContinuousCohomology
noncomputable section
namespace GSsupport
variable (p:ℕ) [Fact p.Prime] (Q:Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
local notation "k" => ZMod p
abbrev discTrivRep : Action (TopModuleCat k) Q := Action.trivial Q (TopModuleCat.of k k)
abbrev discHC := (ContinuousCohomology.homogeneousCochains k Q).obj (discTrivRep p Q)
-- Homogeneous and inhomogeneous two cochains in the concrete complex.
-- In the finite discrete situation no exponential law is needed; maps from Q are continuous.
def homogTwo (f : Q → Q → k) : C(Q, C(Q, C(Q,k))) :=
 ⟨fun g0 => ⟨fun g1 => ⟨fun g2 => f (g0⁻¹*g1) (g1⁻¹*g2), continuous_of_discreteTopology⟩,
   continuous_of_discreteTopology⟩, continuous_of_discreteTopology⟩
def asInvTwo (f:Q→Q→k) : (discHC p Q).X 2 := ⟨homogTwo p Q f, by
  intro g
  -- expect equality of nested maps using trivial action
  change _ = _
  -- inspect goal
  change ((ContinuousCohomology.Iobj (ContinuousCohomology.Iobj (ContinuousCohomology.Iobj (discTrivRep p Q)))).ρ g).hom (homogTwo p Q f) = homogTwo p Q f
  ext x y z
  change f (_ * _) (_ * _) = f _ _
  simp [homogTwo, mul_assoc]
  ⟩


def homogOne (b : Q → k) : C(Q,C(Q,k)) :=
 ⟨fun g0 => ⟨fun g1 => b (g0⁻¹*g1), continuous_of_discreteTopology⟩, continuous_of_discreteTopology⟩
def asInvOne (b : Q → k) : (discHC p Q).X 1 := ⟨homogOne p Q b, by
  intro g
  change ((ContinuousCohomology.Iobj (ContinuousCohomology.Iobj (discTrivRep p Q))).ρ g).hom (homogOne p Q b) = homogOne p Q b
  ext x y
  change b (_ * _) = b _
  simp [mul_assoc]
  ⟩
def homogTwoLM : (Q → Q → k) →ₗ[k] (discHC p Q).X 2 where
 toFun := asInvTwo p Q
 map_add' f g := by
   apply Subtype.ext
   change (homogTwo p Q (f+g)) = (homogTwo p Q f : C(Q,C(Q,C(Q,k)))) + homogTwo p Q g
   ext x y z
   rfl
 map_smul' a f := by
   apply Subtype.ext
   change (homogTwo p Q (a • f)) = a • (homogTwo p Q f)
   ext x y z
   rfl
def homogOneLM : (Q → k) →ₗ[k] (discHC p Q).X 1 where
 toFun := asInvOne p Q
 map_add' b c := by
   apply Subtype.ext
   change homogOne p Q (b+c) = (homogOne p Q b : C(Q,C(Q,k))) + homogOne p Q c
   ext x y
   rfl
 map_smul' a b := by
   apply Subtype.ext
   change homogOne p Q (a • b) = a • homogOne p Q b
   ext x y
   rfl
lemma hom2LM_injective : Function.Injective (homogTwoLM p Q) := by
 intro f f' h
 have h' : (homogTwo p Q f : C(Q,C(Q,C(Q,k)))) = homogTwo p Q f' := congrArg (fun z : (discHC p Q).X 2 => z.1) h
 funext q r
 have hx := congrArg (fun z : C(Q,C(Q,C(Q,k))) => z 1 q (q*r)) h'
 simpa [homogTwo] using hx
lemma hom1LM_injective : Function.Injective (homogOneLM p Q) := by
 intro b b' h
 have h' : homogOne p Q b = homogOne p Q b' := congrArg (fun z : (discHC p Q).X 1 => z.1) h
 funext q
 have hx := congrArg (fun z : C(Q,C(Q,k)) => z 1 q) h'
 simpa [homogOne] using hx
def unhomogTwo (F : (discHC p Q).X 2) (q r : Q) : k :=
  (show C(Q,C(Q,C(Q,k))) from F.1) 1 q (q*r)
def unhomogOne (F : (discHC p Q).X 1) (q : Q) : k :=
  (show C(Q,C(Q,k)) from F.1) 1 q
lemma homogTwo_unhomog (F : (discHC p Q).X 2) : asInvTwo p Q (unhomogTwo p Q F) = F := by
 apply Subtype.ext
 change (homogTwo p Q (unhomogTwo p Q F) : C(Q,C(Q,C(Q,k)))) = F.1
 apply ContinuousMap.ext; intro a
 apply ContinuousMap.ext; intro b
 apply ContinuousMap.ext; intro c
 -- invariance by a⁻¹ at 1,a⁻¹b,a⁻¹c
 have h := F.2 a
 change ((ContinuousCohomology.Iobj (ContinuousCohomology.Iobj (ContinuousCohomology.Iobj (discTrivRep p Q)))).ρ a).hom F.1 = F.1 at h
 have hx := congrArg (fun z : C(Q,C(Q,C(Q,k))) => z a b c) h
 change _ = (show C(Q,C(Q,C(Q,k))) from F.1) a b c
 change (show C(Q,C(Q,C(Q,k))) from F.1) (a⁻¹ * a) (a⁻¹ * b) (a⁻¹ * c) = (show C(Q,C(Q,C(Q,k))) from F.1) a b c at hx
 simpa [homogTwo, unhomogTwo, mul_assoc] using hx -- orientation?
lemma homogOne_unhomog (F : (discHC p Q).X 1) : asInvOne p Q (unhomogOne p Q F) = F := by
 apply Subtype.ext
 change (homogOne p Q (unhomogOne p Q F) : C(Q,C(Q,k))) = F.1
 apply ContinuousMap.ext; intro a
 apply ContinuousMap.ext; intro b
 have h := F.2 a
 change ((ContinuousCohomology.Iobj (ContinuousCohomology.Iobj (discTrivRep p Q))).ρ a).hom F.1 = F.1 at h
 have hx := congrArg (fun z : C(Q,C(Q,k)) => z a b) h
 change _ = (show C(Q,C(Q,k)) from F.1) a b
 change (show C(Q,C(Q,k)) from F.1) (a⁻¹ * a) (a⁻¹ * b) = (show C(Q,C(Q,k)) from F.1) a b at hx
 simpa [homogOne, unhomogOne] using hx

end GSsupport

namespace GSsupport
open CategoryTheory Functor ContinuousMap
open ContinuousCohomology
noncomputable section
variable (p:ℕ) [Fact p.Prime] (Q:Type) [Group Q]
  [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
local notation "k" => ZMod p
/-- The explicit two-bar of `R/JR`, on the nose a degree-two homogeneous
cochain of the complex used by `continuousCohomology`. This is the first
(topological) type conversion in the comparison; it uses only discreteness. -/
def relAsHomogeneous (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (l : Module.Dual k (minimalRel p Q T)) : (discHC p Q).X 2 :=
  asInvTwo p Q (relCocycle p Q T hleft l)
lemma unhomog_relAsHomogeneous (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (l : Module.Dual k (minimalRel p Q T)) (q r : Q) :
    unhomogTwo p Q (relAsHomogeneous p Q T hleft l) q r =
      relCocycle p Q T hleft l q r := by
  simp [unhomogTwo, relAsHomogeneous, asInvTwo, homogTwo]
/-- In particular the dehomogenized cochain satisfies the bar cocycle
identity proved algebraically from `R/JR`. -/
lemma unhomog_rel_condition (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T)
    (l : Module.Dual k (minimalRel p Q T)) (q r s : Q) :
    unhomogTwo p Q (relAsHomogeneous p Q T hleft l) q r +
      unhomogTwo p Q (relAsHomogeneous p Q T hleft l) (q*r) s =
    unhomogTwo p Q (relAsHomogeneous p Q T hleft l) q (r*s) +
      unhomogTwo p Q (relAsHomogeneous p Q T hleft l) r s := by
  simpa [unhomog_relAsHomogeneous] using
    (relCocycle_condition p Q T hleft l q r s)
end
end GSsupport

namespace GSsupport
open CategoryTheory Functor ContinuousMap
open ContinuousCohomology
noncomputable section
variable (p : ℕ) [Fact p.Prime] (Q : Type) [Group Q]
 [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
local notation "k" => ZMod p
/- The definition of `MultiInd.d` is recursive: the new first variable is the
constant term and the rest is the previous differential.  At this degree it
really is the four-term homogeneous differential. Keeping this computation at
functions (rather than a model for cochains) is useful when producing honest
cycles of `continuousCohomology`. -/
lemma discHC_d23_apply (F : (discHC p Q).X 2) (a b c d : Q) :
    (show C(Q,C(Q,C(Q,C(Q,k)))) from
       (((discHC p Q).d 2 3).hom F).1) a b c d =
        (show C(Q,C(Q,C(Q,k))) from F.1) b c d -
        (show C(Q,C(Q,C(Q,k))) from F.1) a c d +
        (show C(Q,C(Q,C(Q,k))) from F.1) a b d -
        (show C(Q,C(Q,C(Q,k))) from F.1) a b c := by
  -- The restriction from `MultiInd` just asks that the resulting function is
  -- invariant.  Its underlying map still is `d 3`.  Peeling one leading
  -- variable at a time keeps the computation robust under the wrappers
  -- `invariants` and `TopModuleCat`.
  change (show C(Q,C(Q,C(Q,C(Q,k)))) from
     (((ContinuousCohomology.invariants k Q).map
        ((ContinuousCohomology.MultiInd.d k Q 3).app
          (GSsupport.discTrivRep p Q))).hom F).1) a b c d = _
  change (show C(Q,C(Q,C(Q,C(Q,k)))) from
     (((ContinuousCohomology.MultiInd.d k Q 3).app
          (GSsupport.discTrivRep p Q)).hom.hom F.1)) a b c d = _
  change (show C(Q,C(Q,C(Q,k))) from F.1) b c d -
       (show C(Q,C(Q,C(Q,k))) from
          (((ContinuousCohomology.MultiInd.d k Q 2).app
            (GSsupport.discTrivRep p Q)).hom.hom
              ((show C(Q,C(Q,C(Q,k))) from F.1) a))) b c d = _
  change (show C(Q,C(Q,C(Q,k))) from F.1) b c d -
    ((show C(Q,C(Q,k)) from ((show C(Q,C(Q,C(Q,k))) from F.1) a)) c d -
      (show C(Q,C(Q,k)) from
       (((ContinuousCohomology.MultiInd.d k Q 1).app
            (GSsupport.discTrivRep p Q)).hom.hom
              ((show C(Q,C(Q,C(Q,k))) from F.1) a b))) c d) = _
  change (show C(Q,C(Q,C(Q,k))) from F.1) b c d -
    ((show C(Q,C(Q,k)) from ((show C(Q,C(Q,C(Q,k))) from F.1) a)) c d -
      ((show C(Q,k) from ((show C(Q,C(Q,C(Q,k))) from F.1) a b)) d -
        (show C(Q,k) from
          (((ContinuousCohomology.MultiInd.d k Q 0).app
            (GSsupport.discTrivRep p Q)).hom.hom
             ((show C(Q,C(Q,C(Q,k))) from F.1) a b c))) d)) = _
  change
    ((show C(Q,C(Q,C(Q,k))) from F.1) b c d) -
      (((show C(Q,C(Q,C(Q,k))) from F.1) a c d) -
        (((show C(Q,C(Q,C(Q,k))) from F.1) a b d) -
          ((show C(Q,C(Q,C(Q,k))) from F.1) a b c))) = _
  abel

/-- The bars built from `R / J R` are genuine cycles in the *actual*
continuous homogeneous complex.  This bridges the inhomogeneous computation
`relCocycle_condition` to the categorical differential `d 2 3`; no modeled
cochain complex is involved. -/
lemma relAsHomogeneous_is_cocycle (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T)
    (l : Module.Dual k (minimalRel p Q T)) :
    ((discHC p Q).d 2 3).hom (relAsHomogeneous p Q T hleft l) = 0 := by
  apply Subtype.ext
  change (show C(Q,C(Q,C(Q,C(Q,k)))) from
       (((discHC p Q).d 2 3).hom (relAsHomogeneous p Q T hleft l)).1) = 0
  apply ContinuousMap.ext; intro a
  apply ContinuousMap.ext; intro b
  apply ContinuousMap.ext; intro c
  apply ContinuousMap.ext; intro d
  change (show C(Q,C(Q,C(Q,C(Q,k)))) from
       (((discHC p Q).d 2 3).hom (relAsHomogeneous p Q T hleft l)).1)
       a b c d = (0 : k)
  rw [discHC_d23_apply]
  simp [relAsHomogeneous, asInvTwo, homogTwo]
  have H := relCocycle_condition p Q T hleft l
       (a⁻¹ * b) (b⁻¹ * c) (c⁻¹ * d)
  simp [mul_assoc] at H
  linear_combination - H
end
end GSsupport

namespace GSsupport
open CategoryTheory Functor ContinuousMap
open ContinuousCohomology
noncomputable section
variable (p : ℕ) [Fact p.Prime] (Q : Type) [Group Q]
 [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
local notation "k" => ZMod p
/-- The same underlying recursive differential gives the familiar three terms
one degree lower. This is separated from cocycles because it describes the
quotient by actual boundaries later. -/
lemma discHC_d12_apply (F : (discHC p Q).X 1) (a b c : Q) :
   (show C(Q,C(Q,C(Q,k))) from (((discHC p Q).d 1 2).hom F).1) a b c =
     (show C(Q,C(Q,k)) from F.1) b c -
     (show C(Q,C(Q,k)) from F.1) a c +
     (show C(Q,C(Q,k)) from F.1) a b := by
  change (show C(Q,C(Q,C(Q,k))) from
    (((ContinuousCohomology.invariants k Q).map
      ((ContinuousCohomology.MultiInd.d k Q 2).app
        (GSsupport.discTrivRep p Q))).hom F).1) a b c = _
  change (show C(Q,C(Q,C(Q,k))) from
     (((ContinuousCohomology.MultiInd.d k Q 2).app
       (GSsupport.discTrivRep p Q)).hom.hom F.1)) a b c = _
  change (show C(Q,C(Q,k)) from F.1) b c -
    (show C(Q,C(Q,k)) from
      (((ContinuousCohomology.MultiInd.d k Q 1).app
         (GSsupport.discTrivRep p Q)).hom.hom
          ((show C(Q,C(Q,k)) from F.1) a))) b c = _
  change (show C(Q,C(Q,k)) from F.1) b c -
    ((show C(Q,k) from ((show C(Q,C(Q,k)) from F.1) a)) c -
      (show C(Q,k) from
        (((ContinuousCohomology.MultiInd.d k Q 0).app
           (GSsupport.discTrivRep p Q)).hom.hom
            ((show C(Q,C(Q,k)) from F.1) a b))) c) = _
  change (show C(Q,C(Q,k)) from F.1) b c -
      ((show C(Q,C(Q,k)) from F.1) a c -
       (show C(Q,C(Q,k)) from F.1) a b) = _
  abel

lemma unhomog_d12 (v : Q → k) (q r : Q) :
 unhomogTwo p Q (((discHC p Q).d 1 2).hom (asInvOne p Q v)) q r =
    v r - v (q*r) + v q := by
  change (show C(Q,C(Q,C(Q,k))) from
     (((discHC p Q).d 1 2).hom (asInvOne p Q v)).1) 1 q (q*r) = _
  rw [discHC_d12_apply]
  simp [asInvOne, homogOne]

lemma unhomog_d12_any (F : (discHC p Q).X 1) (q r : Q) :
 unhomogTwo p Q (((discHC p Q).d 1 2).hom F) q r =
    unhomogOne p Q F r - unhomogOne p Q F (q*r) + unhomogOne p Q F q := by
  nth_rewrite 1 [← homogOne_unhomog p Q F]
  simpa using (unhomog_d12 (p:=p) (Q:=Q) (unhomogOne p Q F) q r)
end
end GSsupport

namespace GSsupport
open CategoryTheory Functor ContinuousMap
open ContinuousCohomology
noncomputable section
variable (p : ℕ) [Fact p.Prime] (Q : Type) [Group Q]
 [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
local notation "k" => ZMod p
/-- In the trivial discrete representation the usual two-bar equation is
exactly, not just a consequence of, lying in the cycles of the homogeneous
complex. The reverse implication uses the four special vertices
`1,q,q*r,(q*r)*s`; the forward one uses invariance to translate arbitrary
vertices back to these. -/
lemma closed_asInvTwo_iff (f : Q → Q → k) :
 ((discHC p Q).d 2 3).hom (asInvTwo p Q f) = 0 ↔
 ∀ q r s : Q, f q r + f (q*r) s = f q (r*s) + f r s := by
 constructor
 · intro h q r s
   have hx := congrArg (fun z : (discHC p Q).X 3 =>
      (show C(Q,C(Q,C(Q,C(Q,k)))) from z.1) 1 q (q*r) ((q*r)*s)) h
   change _ = (0 : k) at hx
   rw [discHC_d23_apply] at hx
   change f (q⁻¹ * (q*r)) ((q*r)⁻¹ * ((q*r)*s)) -
       f (1⁻¹ * (q*r)) ((q*r)⁻¹ * ((q*r)*s)) +
       f (1⁻¹ * q) (q⁻¹ * ((q*r)*s)) -
       f (1⁻¹ * q) (q⁻¹ * (q*r)) = 0 at hx
   simp [mul_assoc] at hx
   linear_combination - hx
 · intro h
   apply Subtype.ext
   change (show C(Q,C(Q,C(Q,C(Q,k)))) from
       (((discHC p Q).d 2 3).hom (asInvTwo p Q f)).1) = 0
   ext a b c d
   change (show C(Q,C(Q,C(Q,C(Q,k)))) from
       (((discHC p Q).d 2 3).hom (asInvTwo p Q f)).1) a b c d = (0 : k)
   rw [discHC_d23_apply]
   change f (b⁻¹ * c) (c⁻¹ * d) - f (a⁻¹ * c) (c⁻¹ * d) +
        f (a⁻¹ * b) (b⁻¹ * d) - f (a⁻¹ * b) (b⁻¹ * c) = 0
   have hh := h (a⁻¹*b) (b⁻¹*c) (c⁻¹*d)
   simp [mul_assoc] at hh
   linear_combination - hh

lemma closed_iff_unhomog (F : (discHC p Q).X 2) :
 ((discHC p Q).d 2 3).hom F = 0 ↔
 ∀ q r s : Q,
   unhomogTwo p Q F q r + unhomogTwo p Q F (q*r) s =
     unhomogTwo p Q F q (r*s) + unhomogTwo p Q F r s := by
  -- no choice of a presentation is needed for this conversion
  nth_rewrite 1 [← homogTwo_unhomog p Q F]
  exact closed_asInvTwo_iff p Q (unhomogTwo p Q F)
end
end GSsupport

namespace GSsupport
open CategoryTheory Functor ContinuousMap
open ContinuousCohomology
noncomputable section
variable (p : ℕ) [Fact p.Prime] (Q : Type) [Group Q]
 [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
local notation "k" => ZMod p
/-- Likewise the *actual* image of `d 1 2` is exactly the elementary
one-cochain coboundaries. Both directions here are useful: it prevents proving
nontriviality only in a simulated bar complex when passing to homology. -/
lemma boundary_iff_unhomog (F : (discHC p Q).X 2) :
 (∃ A : (discHC p Q).X 1, ((discHC p Q).d 1 2).hom A = F) ↔
 (∃ v : Q → k, ∀ q r : Q,
      unhomogTwo p Q F q r = v r - v (q*r) + v q) := by
 constructor
 · rintro ⟨A, rfl⟩
   refine ⟨unhomogOne p Q A, ?_⟩
   exact unhomog_d12_any p Q A
 · rintro ⟨v, hv⟩
   refine ⟨asInvOne p Q v, ?_⟩
   have he : unhomogTwo p Q (((discHC p Q).d 1 2).hom (asInvOne p Q v)) =
       unhomogTwo p Q F := by
     funext q r
     rw [unhomog_d12]
     exact (hv q r).symm
   have hh := congrArg (fun f : Q → Q → k => asInvTwo p Q f) he
   simpa only [homogTwo_unhomog] using hh
end
end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/HomogeneousBridge.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/RelGenerate.lean
section

noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

variable [Finite Q]

-- A left multiple of a relation, as a relation.
def relLeft (T : Finset Q) (a : B) :
    (relSub p Q T) →ₗ[k] (relSub p Q T) :=
{ toFun := fun u =>
    ⟨vecMul p Q T a (u.1 : relFree p Q T), by
      apply (LinearMap.mem_ker).2
      simpa [relMap_mul] using
        (show a * relMap p Q T (u.1 : relFree p Q T) = (0:B) by
          rw [LinearMap.mem_ker.1 u.2]; simp)⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    exact vecMul_add' p Q T a x.1 y.1
  map_smul' := by
    intro c x
    apply Subtype.ext
    -- coefficients are central
    funext i
    simp [vecMul, mul_smul_comm] }

@[simp] lemma relLeft_vec (T : Finset Q) (a:B) (u : relSub p Q T) :
    ((relLeft p Q T a u : relSub p Q T) : relFree p Q T) =
      vecMul p Q T a (u.1 : relFree p Q T) := rfl

lemma relLeft_assoc (T : Finset Q) (a b:B) (u : relSub p Q T) :
    relLeft p Q T a (relLeft p Q T b u) =
      relLeft p Q T (a*b) u := by
  apply Subtype.ext
  exact vecMul_assoc p Q T a b u.1

@[simp] lemma relLeft_one (T : Finset Q) (u : relSub p Q T) :
    relLeft p Q T (1:B) u = u := by
  apply Subtype.ext
  funext i
  simp [relLeft, vecMul]

/-- Fix once and for all lifts of a residue basis of the relation module. -/
def relResidueBasis (T : Finset Q) :=
  Module.finBasis k (minimalRel p Q T)

abbrev rnum (T : Finset Q) := Module.finrank k (minimalRel p Q T)

noncomputable def relLift (T : Finset Q)
    (i : Fin (rnum p Q T)) : relSub p Q T :=
  Classical.choose
    (Submodule.mkQ_surjective
      ((augRel p Q T).comap (relSub p Q T).subtype)
      ((relResidueBasis p Q T) i))

@[simp] lemma mk_relLift (T : Finset Q) (i : Fin (rnum p Q T)) :
    (Submodule.mkQ _ (relLift p Q T i)) =
       ((relResidueBasis p Q T) i) :=
  Classical.choose_spec
    (Submodule.mkQ_surjective
      ((augRel p Q T).comap (relSub p Q T).subtype)
      ((relResidueBasis p Q T) i))

/-- Linear span over the whole algebra of the chosen residue lifts. We keep
coefficients as a finite tuple; this is a `k`-linear map. -/
def relGenerate (T : Finset Q) :
    ((Fin (rnum p Q T)) → B) →ₗ[k] (relSub p Q T) :=
{ toFun := fun v =>
    ∑ i : Fin (rnum p Q T), relLeft p Q T (v i) (relLift p Q T i)
  map_add' := by
    intro v w
    -- linearity of the coefficient on the left
    apply Subtype.ext
    funext j
    simp [relLeft, vecMul, Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro c v
    apply Subtype.ext
    funext j
    simp [relLeft, vecMul, Finset.smul_sum, mul_smul_comm] }

lemma relGenerate_mul (T : Finset Q) (a:B)
    (v : (Fin (rnum p Q T)) → B) :
    relLeft p Q T a (relGenerate p Q T v) =
      relGenerate p Q T (fun i => a * v i) := by
  classical
  -- distribute through the finite sum
  apply Subtype.ext
  funext j
  simp [relGenerate, relLeft, vecMul, Finset.mul_sum, mul_assoc]

/-- Scalar residue coefficients are lifts with constants `c • 1`. -/
lemma residue_in_range (T : Finset Q) (u : relSub p Q T) :
    ∃ w ∈ LinearMap.range (relGenerate p Q T),
      Submodule.Quotient.mk (p :=
        ((augRel p Q T).comap (relSub p Q T).subtype)) w =
      Submodule.Quotient.mk (p :=
        ((augRel p Q T).comap (relSub p Q T).subtype)) u := by
  classical
  let bas := relResidueBasis p Q T
  let c := (bas.repr
       (Submodule.Quotient.mk (p :=
         ((augRel p Q T).comap (relSub p Q T).subtype)) u))
  let v : (Fin (rnum p Q T)) → B :=
      fun i => (c i) • (1:B)
  refine ⟨relGenerate p Q T v, ⟨v, rfl⟩, ?_⟩
  -- apply the quotient map linearly to the finite sum
  change (Submodule.mkQ _)
      (∑ i : Fin (rnum p Q T),
        relLeft p Q T (v i) (relLift p Q T i)) = _
  rw [map_sum]
  -- each constant multiple is the field scalar multiple in the tuple
  have term (i : Fin (rnum p Q T)) :
      relLeft p Q T (v i) (relLift p Q T i) =
          (c i) • relLift p Q T i := by
    apply Subtype.ext
    funext j
    simp [v, relLeft, vecMul]
  simp_rw [term]
  simp_rw [map_smul]
  simp_rw [mk_relLift]
  -- this is the expansion in coordinates of a finite basis
  exact (bas.sum_repr
      (Submodule.Quotient.mk (p :=
         ((augRel p Q T).comap (relSub p Q T).subtype)) u))


lemma relGenerate_stable (T : Finset Q) (a:B) (u : relSub p Q T)
    (hu : u ∈ LinearMap.range (relGenerate p Q T)) :
    relLeft p Q T a u ∈ LinearMap.range (relGenerate p Q T) := by
  rcases hu with ⟨v, rfl⟩
  refine ⟨(fun i => a * v i), ?_⟩
  exact (relGenerate_mul p Q T a v).symm

/-- Every vector in `J^n R` is, modulo `J^(n+1) R`, in the module
spanned by residue lifts. This is the useful constructive Nakayama step. -/
lemma powerRel_split (T : Finset Q) (n : ℕ)
    (x : relFree p Q T) (hx : x ∈ powerRel p Q T n) :
    ∃ w : relSub p Q T,
       w ∈ LinearMap.range (relGenerate p Q T) ∧
       ∃ y : relFree p Q T, y ∈ powerRel p Q T (n+1) ∧
          x = (w.1 : relFree p Q T) + y := by
  classical
  -- first expansion of an augmentation multiple of a residue-zero element
  have gen (b:B) (hb : b ∈ aug p Q ^ n)
      (v : relFree p Q T) (hv : v ∈ relSub p Q T) :
      ∃ w : relSub p Q T,
       w ∈ LinearMap.range (relGenerate p Q T) ∧
       ∃ y : relFree p Q T, y ∈ powerRel p Q T (n+1) ∧
          vecMul p Q T b v = (w.1 : relFree p Q T) + y := by
    let vv : relSub p Q T := ⟨v, hv⟩
    obtain ⟨ww, hwW, heq⟩ := residue_in_range p Q T vv
    have hdiff : (vv - ww) ∈
        (augRel p Q T).comap (relSub p Q T).subtype :=
      ((Submodule.Quotient.eq _).1 heq.symm) -- ww-vv
    -- prefer `vv-ww`; `heq` says `mk ww = mk vv`
    have hdiff' : (vv - ww : relSub p Q T).1 ∈ augRel p Q T := hdiff
    -- multiplication of this augmentation expression moves into the next power
    have bymem : vecMul p Q T b ((vv - ww : relSub p Q T).1) ∈
          powerRel p Q T (n+1) := by
      refine Submodule.span_induction (p:= fun z (_ : z ∈ augRel p Q T) =>
        vecMul p Q T b z ∈ powerRel p Q T (n+1)) ?_ ?_ ?_ ?_ hdiff'
      · intro z hz
        rcases hz with ⟨a, ha, u, hu, rfl⟩
        rw [vecMul_assoc]
        apply Submodule.subset_span
        have hba : b * a ∈ aug p Q ^ (n+1) := by
          have h' : b * a ∈ aug p Q ^ n * aug p Q :=
            Submodule.mul_mem_mul hb ha
          simpa [pow_succ] using h'
        exact ⟨b*a, hba, u, hu, rfl⟩
      · have hz0 : vecMul p Q T b (0: relFree p Q T) = 0 := by
          funext i; simp [vecMul]
        rw [hz0]
        exact (powerRel p Q T (n+1)).zero_mem
      · intro u u' hu hu' iu iv
        rw [vecMul_add']
        exact (powerRel p Q T (n+1)).add_mem iu iv
      · intro c u hu iu
        have he : vecMul p Q T b (c • u) =
            c • vecMul p Q T b u := by funext i; simp [vecMul]
        rw [he]
        exact (powerRel p Q T (n+1)).smul_mem c iu
    let w : relSub p Q T := relLeft p Q T b ww
    have wW : w ∈ LinearMap.range (relGenerate p Q T) :=
      relGenerate_stable p Q T b ww hwW
    refine ⟨w, wW,
      vecMul p Q T b ((vv - ww : relSub p Q T).1), bymem, ?_⟩
    funext i
    change b * v i = _
    simp [w, relLeft, vecMul]
    -- scalar distributivity
    noncomm_ring
  refine Submodule.span_induction (p:= fun x (_:x ∈ powerRel p Q T n) =>
    ∃ w : relSub p Q T,
       w ∈ LinearMap.range (relGenerate p Q T) ∧
       ∃ y : relFree p Q T, y ∈ powerRel p Q T (n+1) ∧
          x = (w.1 : relFree p Q T) + y) ?_ ?_ ?_ ?_ hx
  · intro z hz
    rcases hz with ⟨b, hb, v, hv, rfl⟩
    exact gen b hb v hv
  · refine ⟨0, ?_, 0, (powerRel p Q T (n+1)).zero_mem, ?_⟩
    · exact ⟨0, by simp⟩
    · simp
  · intro u v hu hv iu iv
    rcases iu with ⟨wu,hwu,yu,hyu,eu⟩
    rcases iv with ⟨wv,hwv,yv,hyv,ev⟩
    refine ⟨wu+wv, (LinearMap.range (relGenerate p Q T)).add_mem hwu hwv,
      yu+yv, (powerRel p Q T (n+1)).add_mem hyu hyv, ?_⟩
    rw [eu, ev]
    -- reorder the four summands in the ambient additive group
    
    change (wu.1 : relFree p Q T) + yu + ((wv.1 : relFree p Q T) + yv) =
       (wu.1 + wv.1) + (yu+yv)
    abel
  · intro c u hu iu
    rcases iu with ⟨w,hw,y,hy,ey⟩
    refine ⟨c • w, (LinearMap.range (relGenerate p Q T)).smul_mem c hw,
       c • y, (powerRel p Q T (n+1)).smul_mem c hy, ?_⟩
    rw [ey]
    -- distributivity, and subtype coefficients forget definitionally
    change c • ((w.1 : relFree p Q T) + y) = _
    rw [smul_add]
    rfl

/-- The residue lifts generate all honest relations (finite Nakayama).
We iterate the preceding split along the nilpotent augmentation ideal. -/
lemma relGenerate_surjective (hp : IsPGroup p Q) (T : Finset Q) :
    Function.Surjective (relGenerate p Q T) := by
  classical
  obtain ⟨N, hN⟩ := aug_nilpotent p Q hp
  have pbot : powerRel p Q T N =
      (⊥ : Submodule k (relFree p Q T)) := by
    apply le_antisymm
    · apply Submodule.span_le.2
      intro x hx
      rcases hx with ⟨a, ha, u, hu, rfl⟩
      rw [hN] at ha
      have az : a = (0:B) := by simpa using ha
      subst a
      change vecMul p Q T (0:B) u ∈ (⊥ : Submodule k (relFree p Q T))
      change vecMul p Q T (0:B) u = 0
      funext i
      simp [vecMul]
    · exact bot_le
  intro u
  have iter : ∀ n : ℕ, ∀ (v : relFree p Q T),
      v ∈ powerRel p Q T 0 →
      ∃ w : relSub p Q T,
        w ∈ LinearMap.range (relGenerate p Q T) ∧
        ∃ y : relFree p Q T, y ∈ powerRel p Q T n ∧
           v = (w.1 : relFree p Q T) + y := by
    intro n
    induction n with
    | zero =>
      intro v hv
      exact ⟨0, ⟨0, by simp⟩, v, hv, by simp⟩
    | succ n ih =>
      intro v hv
      rcases ih v hv with ⟨w, hw, y, hy, ev⟩
      rcases powerRel_split p Q T n y hy with ⟨w',hw',z,hz,ez⟩
      refine ⟨w+w', (LinearMap.range (relGenerate p Q T)).add_mem hw hw',
        z, hz, ?_⟩
      rw [ev, ez]
      -- regroup in the ambient tuple
      change (w.1 : relFree p Q T) + ((w'.1 : relFree p Q T) + z) =
        (w.1 + w'.1) + z
      abel
  have u0 : (u.1 : relFree p Q T) ∈ powerRel p Q T 0 :=
    relSub_mem_powerRel_zero p Q T u.1 u.2
  rcases iter N (u.1 : relFree p Q T) u0 with ⟨w, hw, y, hy, ey⟩
  rw [pbot] at hy
  have yz : y = 0 := by simpa using hy
  subst y
  have e : w = u := by
    apply Subtype.ext
    simpa using ey.symm
  rw [e] at hw
  exact hw

lemma finrank_relSub_le_top_mul_card (hp : IsPGroup p Q) (T : Finset Q) :
    Module.finrank k (relSub p Q T) ≤
       Module.finrank k (minimalRel p Q T) * Nat.card Q := by
  classical
  have su := relGenerate_surjective p Q hp T
  have h := LinearMap.finrank_le_finrank_of_surjective su
  -- the source is the finite product of copies of the group algebra
  have hb : Module.finrank k B = Nat.card Q :=
    finrank_algebra_eq_card p Q
  simpa [rnum, Module.finrank_pi_fintype, hb, Finset.mul_sum,
    mul_comm] using h

end GSsupport

noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q
variable [Finite Q]

/-- The fixed residue lifts have at least one augmentation in every
coordinate, for a minimal first presentation.  Stating this once makes
filtered multiplication bookkeeping independent of the quotient model of
`minimalRel`. -/
lemma relLift_coordinates (T : Finset Q)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤)
    (i : Fin (rnum p Q T)) (j : (↥T)) :
    ((relLift p Q T i : relSub p Q T) : relFree p Q T) j ∈ aug p Q := by
  have h := relKernel_coordinates p Q T hcard hspan
    ((relLift p Q T i : relSub p Q T) : relFree p Q T)
    (LinearMap.mem_ker.1 (relLift p Q T i).2)
  exact h j

/-- Multiplying one of the chosen lifts by a coefficient in `J^m` produces
a tuple in degree `m+1`.  This is the part of the translated map that is
strict without any assertion about intersections. -/
lemma relGenerate_power_mem (T : Finset Q) (m : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤)
    (v : (Fin (rnum p Q T)) → (↥(aug p Q ^ m))) :
    ((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T) :
       relFree p Q T) ∈ freePow p Q T (m+1) := by
  classical
  intro j
  have each (i : Fin (rnum p Q T)) :
      (v i : B) *
        (((relLift p Q T i : relSub p Q T) : relFree p Q T) j)
          ∈ aug p Q ^ (m+1) := by
    have ha : (v i : B) ∈ aug p Q ^ m := (v i).property
    have hu : (((relLift p Q T i : relSub p Q T) : relFree p Q T) j) ∈
        aug p Q := relLift_coordinates p Q T hcard hspan i j
    have hpw : (v i : B) *
        (((relLift p Q T i : relSub p Q T) : relFree p Q T) j) ∈
        aug p Q ^ m * aug p Q := Submodule.mul_mem_mul ha hu
    simpa [pow_succ] using hpw
  have hsum : (∑ i : Fin (rnum p Q T), (v i : B) *
        (((relLift p Q T i : relSub p Q T) : relFree p Q T) j))
          ∈ aug p Q ^ (m+1) :=
    Submodule.sum_mem _ (fun i hi => each i)
  simpa [relGenerate, relLeft, vecMul] using hsum

/-- Coefficients in the next power already die in the intervening kernel
layer.  It is worth keeping this fact in ambient tuples: it avoids choosing
any linear section of the augmentation quotient. -/
lemma relGenerate_power_succ_range (T : Finset Q) (m : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤)
    (v : (Fin (rnum p Q T)) → (↥(aug p Q ^ (m+1)))) :
    ∃ y : (LinearMap.ker (stepMap p Q T (m+1))),
      (((kerInclusion p Q T m) y :
          LinearMap.ker (stepMap p Q T m)) :
          (freePow p Q T (m+1))) =
        ⟨((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T) :
             relFree p Q T),
          fun j => pow_antitone_succ p Q m
            ((relGenerate_power_mem p Q T (m+1) hcard hspan v) j)⟩ := by
  classical
  -- The same vector, viewed one power deeper, is already a kernel element;
  -- forgetting a power is exactly `kerInclusion`.
  let zvec : relFree p Q T :=
    ((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T) :
        relFree p Q T)
  have zpow : zvec ∈ freePow p Q T ((m+1)+1) :=
    relGenerate_power_mem p Q T (m+1) hcard hspan v
  have zker : relMap p Q T zvec = (0:B) :=
    LinearMap.mem_ker.1
      ((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T).2)
  let z : freePow p Q T ((m+1)+1) := ⟨zvec, zpow⟩
  have zz : z ∈ LinearMap.ker (stepMap p Q T (m+1)) := by
    apply (LinearMap.mem_ker).2
    apply Subtype.ext
    simpa only [stepMap_val, Submodule.coe_zero] using zker
  refine ⟨⟨z, zz⟩, ?_⟩
  rfl

/-- The always-defined linear map from actual degree-`m` coefficients to the
kernel layer.  Surjectivity of its range is the genuine filtered-generation
question; separating this map is useful, since the construction and its
next-power kernel are elementary. -/
noncomputable def relPowerClass (T : Finset Q) (m : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    ((Fin (rnum p Q T)) → (↥(aug p Q ^ m))) →ₗ[k]
      (kernelLayer p Q T m) := by
  classical
  -- first form a kernel element in `freePow (m+1)`
  let toKer : ((Fin (rnum p Q T)) → (↥(aug p Q ^ m))) →ₗ[k]
      (LinearMap.ker (stepMap p Q T m)) :=
    { toFun := fun v =>
        ⟨⟨((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T) :
             relFree p Q T),
            relGenerate_power_mem p Q T m hcard hspan v⟩,
          by
            apply (LinearMap.mem_ker).2
            apply Subtype.ext
            have hz : relMap p Q T
                (((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T) :
                   relFree p Q T)) = (0:B) :=
                LinearMap.mem_ker.1
                  ((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T).2)
            simpa only [stepMap_val, Submodule.coe_zero] using hz⟩
      map_add' := by
        intro v w
        apply Subtype.ext
        apply Subtype.ext
        -- `relGenerate` is linear over `k`; coercions of the power subtype
        -- commute with addition pointwise.
        have eqv : (fun i => ((v+w) i : B)) =
            (fun i => (v i : B)) + (fun i => (w i : B)) := rfl
        change (((relGenerate p Q T)
             (fun i => ((v+w) i : B)) : relSub p Q T) :
                 relFree p Q T) = _
        rw [eqv, map_add]
        rfl
      map_smul' := by
        intro c v
        apply Subtype.ext
        apply Subtype.ext
        have eqv : (fun i => ((c • v) i : B)) =
            c • (fun i => (v i : B)) := rfl
        change (((relGenerate p Q T)
             (fun i => ((c • v) i : B)) : relSub p Q T) :
                 relFree p Q T) = _
        rw [eqv, map_smul]
        rfl }
  exact (Submodule.mkQ (LinearMap.range (kerInclusion p Q T m))).comp toKer

@[simp] lemma relPowerClass_val (T : Finset Q) (m : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤)
    (v : (Fin (rnum p Q T)) → (↥(aug p Q ^ m))) :
    relPowerClass p Q T m hcard hspan v =
      Submodule.Quotient.mk
        (show LinearMap.ker (stepMap p Q T m) from
          ⟨⟨((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T) :
                relFree p Q T),
              relGenerate_power_mem p Q T m hcard hspan v⟩,
            by
              apply (LinearMap.mem_ker).2
              apply Subtype.ext
              have hz : relMap p Q T
                  (((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T) :
                    relFree p Q T)) = (0:B) :=
                LinearMap.mem_ker.1
                  ((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T).2)
              simpa only [stepMap_val, Submodule.coe_zero] using hz⟩) := rfl

end GSsupport

noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q
variable [Finite Q]

/-- Taking the class of a tuple of actual power coefficients, coordinatewise. -/
def coeffClass (T : Finset Q) (m : ℕ) :
    ((Fin (rnum p Q T)) → (↥(aug p Q ^ m))) →ₗ[k]
       ((Fin (rnum p Q T)) → (augLayer p Q m)) :=
  { toFun := fun v i =>
        Submodule.Quotient.mk (p :=
          ((aug p Q ^ (m+1)).comap (aug p Q ^ m).subtype)) (v i)
    map_add' := by intros; ext i; exact (Submodule.mkQ _).map_add _ _
    map_smul' := by intros; ext i; exact (Submodule.mkQ _).map_smul _ _ }

lemma coeffClass_surjective (T : Finset Q) (m : ℕ) :
    Function.Surjective (coeffClass p Q T m) := by
  classical
  intro w
  choose v hv using fun i : Fin (rnum p Q T) =>
    Submodule.mkQ_surjective
      ((aug p Q ^ (m+1)).comap (aug p Q ^ m).subtype) (w i)
  refine ⟨fun i => v i, ?_⟩
  funext i
  exact hv i

/-- The next power is in the kernel of the power-class map. -/
lemma relPowerClass_zero_of_coeff_kernel (T : Finset Q) (m : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤)
    (v : (Fin (rnum p Q T)) → (↥(aug p Q ^ m)))
    (hv : coeffClass p Q T m v = 0) :
    relPowerClass p Q T m hcard hspan v = 0 := by
  classical
  -- read each zero quotient as membership in `J^(m+1)`
  have hver (i : Fin (rnum p Q T)) : (v i : B) ∈ aug p Q ^ (m+1) := by
    have hi : (coeffClass p Q T m v) i =
        (0 : (augLayer p Q m)) := congrFun hv i
    have hq := (Submodule.Quotient.mk_eq_zero
       ((aug p Q ^ (m+1)).comap (aug p Q ^ m).subtype)).1 hi
    exact hq
  let w : (Fin (rnum p Q T)) → (↥(aug p Q ^ (m+1))) :=
      fun i => ⟨(v i : B), hver i⟩
  obtain ⟨y, hy⟩ := relGenerate_power_succ_range p Q T m hcard hspan w
  -- compare the shallow kernel element used by `relPowerClass` with this
  -- deeper one. They have literally the same ambient tuple.
  change (Submodule.mkQ (LinearMap.range (kerInclusion p Q T m)))
      (show LinearMap.ker (stepMap p Q T m) from
        ⟨⟨((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T) :
               relFree p Q T),
             relGenerate_power_mem p Q T m hcard hspan v⟩, by
            apply (LinearMap.mem_ker).2
            apply Subtype.ext
            have hz : relMap p Q T
                (((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T) :
                    relFree p Q T)) = (0:B) :=
              LinearMap.mem_ker.1 ((relGenerate p Q T
                (fun i => (v i : B)) : relSub p Q T).2)
            simpa only [stepMap_val, Submodule.coe_zero] using hz⟩) = 0
  apply (Submodule.Quotient.mk_eq_zero _).2
  -- equality in the shallow subtype is extensional on the tuple
  refine ⟨y, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have hh := congrArg
    (fun z : freePow p Q T (m+1) => (z : relFree p Q T)) hy
  simpa [w] using hh

/-- A completely canonical translated map after quotienting the
coefficients. No splittings are chosen. The only further fact a strictness
argument would have to supply is that `relPowerClass` is onto. -/
noncomputable def translatedClass (T : Finset Q) (m : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    ((Fin (rnum p Q T)) → (augLayer p Q m)) →ₗ[k]
       (kernelLayer p Q T m) := by
  classical
  let f := coeffClass p Q T m
  let g := relPowerClass p Q T m hcard hspan
  have kill : LinearMap.ker f ≤ LinearMap.ker g := by
    intro v hv
    apply (LinearMap.mem_ker).2
    exact relPowerClass_zero_of_coeff_kernel p Q T m hcard hspan v
      ((LinearMap.mem_ker).1 hv)
  let gbar : (( (Fin (rnum p Q T)) → (↥(aug p Q ^ m))) ⧸
          LinearMap.ker f) →ₗ[k] (kernelLayer p Q T m) :=
      (LinearMap.ker f).liftQ g kill
  let ef : (((Fin (rnum p Q T)) → (↥(aug p Q ^ m))) ⧸
          LinearMap.ker f) ≃ₗ[k]
         ((Fin (rnum p Q T)) → (augLayer p Q m)) :=
      f.quotKerEquivOfSurjective (coeffClass_surjective p Q T m)
  exact gbar.comp ef.symm.toLinearMap

/-- Dividing the actual-power candidate by coordinate classes loses no
surjectivity. This packages the harmless quotient bookkeeping; the honest
filtered issue is exactly the surjectivity of `relPowerClass`. -/
lemma translatedClass_surj_of_power (T : Finset Q) (m : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤)
    (hpow : Function.Surjective
       (relPowerClass p Q T m hcard hspan)) :
    Function.Surjective (translatedClass p Q T m hcard hspan) := by
  classical
  let f := coeffClass p Q T m
  let g := relPowerClass p Q T m hcard hspan
  have kill : LinearMap.ker f ≤ LinearMap.ker g := by
    intro v hv
    apply (LinearMap.mem_ker).2
    exact relPowerClass_zero_of_coeff_kernel p Q T m hcard hspan v
      ((LinearMap.mem_ker).1 hv)
  let gbar : ((((Fin (rnum p Q T)) → (↥(aug p Q ^ m))) ⧸
          LinearMap.ker f)) →ₗ[k] (kernelLayer p Q T m) :=
      (LinearMap.ker f).liftQ g kill
  let ef : ((((Fin (rnum p Q T)) → (↥(aug p Q ^ m))) ⧸
          LinearMap.ker f)) ≃ₗ[k]
         ((Fin (rnum p Q T)) → (augLayer p Q m)) :=
      f.quotKerEquivOfSurjective (coeffClass_surjective p Q T m)
  intro z
  obtain ⟨v, hv⟩ := hpow z
  refine ⟨ef (Submodule.Quotient.mk v), ?_⟩
  -- both definitions reduce to `g v` on a quotient representative
  change gbar (ef.symm (ef (Submodule.Quotient.mk v))) = z
  rw [ef.symm_apply_apply]
  change g v = z
  exact hv

end GSsupport

noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q
variable [Finite Q]

/-- Generation can be made strict for the honest `J^m R` subspace (as
opposed to the intersection with a free power). This useful half of the
filtered question follows just by distributing coefficients; no intersection
assertion is involved. -/
lemma powerRel_exact_generate (hp : IsPGroup p Q) (T : Finset Q) (m : ℕ) (hm : 0 < m)
    (x : relFree p Q T) (hx : x ∈ powerRel p Q T m) :
    ∃ v : (Fin (rnum p Q T)) → (↥(aug p Q ^ m)),
       ((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T) :
          relFree p Q T) = x := by
  classical
  have rightmul (a b : B) (ha : a ∈ aug p Q ^ m) :
       a * b ∈ aug p Q ^ m := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    exact all_right p Q (aug p Q ^ (n+1)) (pow_rightInv p Q n)
      a b ha
  refine Submodule.span_induction (p:= fun x (_:x ∈ powerRel p Q T m) =>
    ∃ v : (Fin (rnum p Q T)) → (↥(aug p Q ^ m)),
       ((relGenerate p Q T (fun i => (v i : B)) : relSub p Q T) :
          relFree p Q T) = x) ?_ ?_ ?_ ?_ hx
  · intro z hz
    rcases hz with ⟨a,ha,u,hu,rfl⟩
    obtain ⟨c, hc⟩ := relGenerate_surjective p Q hp T (⟨u, hu⟩ : relSub p Q T)
    let v : (Fin (rnum p Q T)) → (↥(aug p Q ^ m)) :=
      fun i => ⟨a * c i, rightmul a (c i) ha⟩
    refine ⟨v, ?_⟩
    have ee := relGenerate_mul p Q T a c
    rw [hc] at ee
    have hh := congrArg (fun z : relSub p Q T => (z.1 : relFree p Q T)) ee
    simpa [v] using hh.symm
  · refine ⟨0, ?_⟩
    -- the zero tuple is mapped to zero
    exact (congrArg (fun z : relSub p Q T => (z.1 : relFree p Q T))
      ((relGenerate p Q T).map_zero))
  · intro u v hu hv iu iv
    rcases iu with ⟨a,ha⟩
    rcases iv with ⟨b,hb⟩
    refine ⟨a+b, ?_⟩
    change (((relGenerate p Q T)
       (fun i => ((a+b) i : B)) : relSub p Q T) :
         relFree p Q T) = u+v
    have eqv : (fun i => ((a+b) i : B)) =
        (fun i => (a i : B)) + (fun i => (b i : B)) := rfl
    rw [eqv, map_add]
    change ((((relGenerate p Q T) (fun i => (a i : B)) :
         relSub p Q T) : relFree p Q T) +
      (((relGenerate p Q T) (fun i => (b i : B)) :
         relSub p Q T) : relFree p Q T)) = _
    rw [ha, hb]
  · intro c u hu iu
    rcases iu with ⟨a,ha⟩
    refine ⟨c • a, ?_⟩
    change (((relGenerate p Q T)
       (fun i => ((c • a) i : B)) : relSub p Q T) :
         relFree p Q T) = c • u
    have eqv : (fun i => ((c • a) i : B)) =
        c • (fun i => (a i : B)) := rfl
    rw [eqv, map_smul]
    change c • (((relGenerate p Q T) (fun i => (a i : B)) :
       relSub p Q T) : relFree p Q T) = _
    rw [ha]

end GSsupport

noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q
variable [Finite Q]

/-- The very simple forward filtration fact for the chosen lifts: a tuple of
coefficients in `J^m` certainly gives a vector of the honest span `J^m R`.
It is only the converse intersection in a *free* power which is delicate.
Putting this direction in ambient tuples is useful when a possible
counterexample has been expanded by Nakayama generation. -/
lemma relGenerate_mem_powerRel (T : Finset Q) (m : ℕ)
    (c : (Fin (rnum p Q T)) → B)
    (hc : ∀ i, c i ∈ aug p Q ^ m) :
    (((relGenerate p Q T c : relSub p Q T) : relFree p Q T)) ∈
      powerRel p Q T m := by
  classical
  -- each summand is one of the displayed generators of the span
  have each (i : Fin (rnum p Q T)) :
      (((relLeft p Q T (c i) (relLift p Q T i) : relSub p Q T) :
          relFree p Q T)) ∈ powerRel p Q T m := by
    apply Submodule.subset_span
    exact ⟨c i, hc i,
      (((relLift p Q T i : relSub p Q T) : relFree p Q T)),
      (relLift p Q T i).2, rfl⟩
  -- `relGenerate` is literally the finite sum in the relation subtype.
  change (((∑ i : Fin (rnum p Q T),
      relLeft p Q T (c i) (relLift p Q T i) : relSub p Q T) :
        relSub p Q T) : relFree p Q T) ∈ powerRel p Q T m
  -- coe of that sum is the sum in the ambient tuple.
  have hs : (∑ i : Fin (rnum p Q T),
      (((relLeft p Q T (c i) (relLift p Q T i) : relSub p Q T) :
          relFree p Q T))) ∈ powerRel p Q T m :=
    Submodule.sum_mem _ (fun i hi => each i)
  simpa using hs

end GSsupport

end
end
end
end
end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/RelGenerate.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Cumulative.lean
section

noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q] [Finite Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- Relations with all their coordinates in a prescribed power.  In contrast to
`powerRel` this is the *intersection* filtration; making it explicit avoids
silently asserting strictness of Nakayama generators. -/
def relInter (T : Finset Q) (n : ℕ) : Submodule k (relSub p Q T) :=
  (freePow p Q T n).comap (relSub p Q T).subtype

@[simp] lemma mem_relInter (T : Finset Q) (n : ℕ) (u : relSub p Q T) :
    u ∈ relInter p Q T n ↔
      (u.1 : relFree p Q T) ∈ freePow p Q T n := Iff.rfl

/-- Coefficient tuples in a uniform deep power. -/
def deepCoeff (T : Finset Q) (n : ℕ) :
    Submodule k ((Fin (rnum p Q T)) → B) :=
{ carrier := {v | ∀ i, v i ∈ aug p Q ^ n}
  add_mem' := by intros v w hv hw i; exact (aug p Q ^ n).add_mem (hv i) (hw i)
  zero_mem' := by intro i; exact (aug p Q ^ n).zero_mem
  smul_mem' := by intro c v hv i; exact (aug p Q ^ n).smul_mem c (hv i) }

@[simp] lemma mem_deepCoeff (T : Finset Q) (n : ℕ)
    (v : (Fin (rnum p Q T)) → B) :
    v ∈ deepCoeff p Q T n ↔ ∀ i, v i ∈ aug p Q ^ n := Iff.rfl

/-- A deep tuple of coefficients maps to a relation in the next intersection,
without any strictness assumption. -/
lemma generate_deep_mem_relInter (T : Finset Q) (n : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤)
    (v : (Fin (rnum p Q T)) → B) (hv : v ∈ deepCoeff p Q T n) :
    relGenerate p Q T v ∈ relInter p Q T (n+1) := by
  -- use the coordinatewise multiplicative estimate, which needs no
  -- filtered-generation statement in the other direction.
  let vv : (Fin (rnum p Q T)) → (↥(aug p Q ^ n)) :=
    fun i => ⟨v i, hv i⟩
  change ((relGenerate p Q T v : relSub p Q T) : relFree p Q T) ∈
      freePow p Q T (n+1)
  simpa [vv] using
    (relGenerate_power_mem p Q T n hcard hspan vv)

/-- Surjection onto the cumulative intersection quotient. The kernel contains
all the deep coefficient tuples (`deepCoeff_le_ker` below); unlike the false
single-layer strictness assertion this only uses finite Nakayama on the *whole*
relation. -/
def cumulativeGenerate (T : Finset Q) (n : ℕ) :
    ((Fin (rnum p Q T)) → B) →ₗ[k] ((relSub p Q T) ⧸ (relInter p Q T (n+1))) :=
  (Submodule.mkQ (relInter p Q T (n+1))).comp (relGenerate p Q T)

lemma cumulativeGenerate_surjective (hp : IsPGroup p Q)
    (T : Finset Q) (n : ℕ) :
    Function.Surjective (cumulativeGenerate p Q T n) := by
  intro z
  obtain ⟨u, rfl⟩ :=
    Submodule.mkQ_surjective (relInter p Q T (n+1)) z
  obtain ⟨v, hv⟩ := relGenerate_surjective p Q hp T u
  refine ⟨v, ?_⟩
  change Submodule.mkQ (relInter p Q T (n+1)) (relGenerate p Q T v) = _
  rw [hv]

lemma deepCoeff_le_ker_cumulativeGenerate (T : Finset Q) (n : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    deepCoeff p Q T n ≤ LinearMap.ker (cumulativeGenerate p Q T n) := by
  intro v hv
  apply (LinearMap.mem_ker).2
  change Submodule.mkQ (relInter p Q T (n+1))
      (relGenerate p Q T (v : (Fin (rnum p Q T)) → B)) = 0
  exact (Submodule.Quotient.mk_eq_zero _).2
    (generate_deep_mem_relInter p Q T n hcard hspan v hv)

/-- Product version of a power, convenient for dimension counts. -/
def deepCoeffEquiv (T : Finset Q) (n : ℕ) :
    (↥(deepCoeff p Q T n)) ≃ₗ[k]
      ((Fin (rnum p Q T)) → (↥(aug p Q ^ n))) :=
{ toFun := fun v i => ⟨v.1 i, v.2 i⟩
  invFun := fun v => ⟨(fun i => (v i : B)), fun i => (v i).2⟩
  left_inv := by intro v; ext i; rfl
  right_inv := by intro v; funext i; rfl
  map_add' := by intros v w; rfl
  map_smul' := by intros c v; rfl }

@[simp] lemma finrank_deepCoeff (T : Finset Q) (n : ℕ) :
    Module.finrank k (deepCoeff p Q T n) =
      rnum p Q T * Module.finrank k (↥(aug p Q ^ n)) := by
  classical
  rw [LinearEquiv.finrank_eq (deepCoeffEquiv p Q T n)]
  simpa [Module.finrank_pi_fintype]

/-- Honest cumulative estimate.  Notice the partial sum hidden in
`finrank (J^n)`: this does **not** imply surjectivity onto each individual
associated-graded layer by coefficients in exactly `J^(n-1)`. -/
lemma cumulative_quotient_estimate (hp : IsPGroup p Q)
    (T : Finset Q) (n : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    Module.finrank k ((relSub p Q T) ⧸ (relInter p Q T (n+1))) +
      rnum p Q T * Module.finrank k (↥(aug p Q ^ n)) ≤
        rnum p Q T * Module.finrank k B := by
  let f := cumulativeGenerate p Q T n
  have hs := cumulativeGenerate_surjective p Q hp T n
  have hker : deepCoeff p Q T n ≤ LinearMap.ker f :=
    deepCoeff_le_ker_cumulativeGenerate p Q T n hcard hspan
  have hrange := LinearMap.finrank_range_add_finrank_ker f
  have hk : Module.finrank k (deepCoeff p Q T n) ≤
      Module.finrank k (LinearMap.ker f) := Submodule.finrank_mono hker
  have hr : Module.finrank k (↥(LinearMap.range f)) =
      Module.finrank k ((relSub p Q T) ⧸ (relInter p Q T (n+1))) := by
    rw [LinearMap.range_eq_top.mpr hs]
    exact finrank_top k _
  have hdom : Module.finrank k ((Fin (rnum p Q T)) → B) =
      rnum p Q T * Module.finrank k B := by
    simp [Module.finrank_pi_fintype]
  rw [hr, hdom] at hrange
  rw [← finrank_deepCoeff p Q T n]
  omega

/-- A restricted kernel is exactly a relation in the intersection.  This is an
isomorphism of ordinary `k`-spaces; it avoids any topological/continuous
packaging around the coefficient powers. -/
def stepKerInterEquiv (T : Finset Q) (m : ℕ) :
    (LinearMap.ker (stepMap p Q T m)) ≃ₗ[k]
      (relInter p Q T (m+1)) :=
{ toFun := fun x =>
    ⟨stepKerToRel p Q T m x, by
      change ((x.1 : freePow p Q T (m+1)) : relFree p Q T) ∈
        freePow p Q T (m+1)
      exact x.1.2⟩
  invFun := fun u =>
    ⟨⟨(u.1.1 : relFree p Q T), u.2⟩,
      by
        apply (LinearMap.mem_ker).2
        apply Subtype.ext
        have hz : relMap p Q T ((u.1.1 : relFree p Q T)) = (0:B) :=
          LinearMap.mem_ker.1 u.1.2
        simpa only [stepMap_val, Submodule.coe_zero] using hz⟩
  left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro u; apply Subtype.ext; apply Subtype.ext; rfl
  map_add' := by intros x y; rfl
  map_smul' := by intros c x; rfl }

@[simp] lemma finrank_relInter_step (T : Finset Q) (m : ℕ) :
    Module.finrank k (relInter p Q T (m+1)) =
      stepKernelRank p Q T m := by
  -- choose direction to avoid rewriting the reducible abbreviation
  simpa [stepKernelRank] using
    (LinearEquiv.finrank_eq (stepKerInterEquiv p Q T m)).symm

/-- For a minimal first presentation every relation is already in the first
free-coordinate power; this is the one point where minimality of `T` enters the
identification of the cumulative quotient with a sum of kernel drops. -/
lemma relInter_one_eq_top (T : Finset Q)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    relInter p Q T 1 = ⊤ := by
  apply top_unique
  intro u hu
  change ((u : relSub p Q T).1 : relFree p Q T) ∈ freePow p Q T 1
  have hc := relKernel_coordinates p Q T hcard hspan
    ((u : relSub p Q T).1 : relFree p Q T)
    (LinearMap.mem_ker.1 (u : relSub p Q T).2)
  intro i
  simpa using (hc i)

lemma finrank_relSub_eq_step0 (T : Finset Q)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    Module.finrank k (relSub p Q T) = stepKernelRank p Q T 0 := by
  have h := finrank_relInter_step p Q T 0
  have he := relInter_one_eq_top p Q T hcard hspan
  -- rewrite the top submodule back to the ambient relation space
  rw [he, finrank_top k _] at h
  simpa using h

/-- Prefix sum of all intervening kernel layers. -/
lemma prefix_layers_add_step (T : Finset Q) (m : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    (∑ i ∈ Finset.range (m+1),
      Module.finrank k (kernelLayer p Q T i)) +
        stepKernelRank p Q T (m+1) =
          Module.finrank k (relSub p Q T) := by
  classical
  induction m with
  | zero =>
      have h := finrank_kernelLayer p Q T 0
      have h0 := finrank_relSub_eq_step0 p Q T hcard hspan
      -- normalize the singleton prefix
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.sum_range_one, Nat.zero_add] -- may simplify too far
      -- expect goal `L0 + K1 = _`
      simpa [h0] using h
  | succ m ih =>
      have hm := finrank_kernelLayer p Q T (m+1)
      -- include the new summand immediately before the residual kernel
      rw [Finset.sum_range_succ]
      -- this `rw` selects the prefix; re-associate to apply `hm`
      calc
        (_ + Module.finrank k (kernelLayer p Q T (m+1))) +
              stepKernelRank p Q T (m+1+1) =
            (∑ i ∈ Finset.range (m+1), Module.finrank k (kernelLayer p Q T i)) +
              (Module.finrank k (kernelLayer p Q T (m+1)) +
                stepKernelRank p Q T ((m+1)+1)) := by ac_rfl
        _ = (∑ i ∈ Finset.range (m+1), Module.finrank k (kernelLayer p Q T i)) +
              stepKernelRank p Q T (m+1) := by rw [hm]
        _ = _ := ih

/-- The quotient by the `(m+2)`th intersection has the *sum* of earlier
kernel-layer dimensions.  This is the right cumulative substitute for strict
filtered generation. -/
lemma finrank_relInter_quotient_prefix (T : Finset Q) (m : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    Module.finrank k ((relSub p Q T) ⧸ (relInter p Q T (m+1+1))) =
      ∑ i ∈ Finset.range (m+1), Module.finrank k (kernelLayer p Q T i) := by
  have hq := Submodule.finrank_quotient_add_finrank (relInter p Q T (m+1+1))
  have hi := finrank_relInter_step p Q T (m+1)
  have hpre := prefix_layers_add_step p Q T m hcard hspan
  rw [hi] at hq
  omega

/-- Cumulative layer bound in the form that is safe without false strictness.
Subtracting consecutive such inequalities is **not** valid: only the prefix is
controlled. -/
lemma prefix_kernelLayer_estimate (hp : IsPGroup p Q)
    (T : Finset Q) (m : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    (∑ i ∈ Finset.range (m+1), Module.finrank k (kernelLayer p Q T i)) +
      rnum p Q T * Module.finrank k (↥(aug p Q ^ (m+1))) ≤
        rnum p Q T * Module.finrank k B := by
  have h := cumulative_quotient_estimate p Q hp T (m+1) hcard hspan
  have he := finrank_relInter_quotient_prefix p Q T m hcard hspan
  -- normalize the power index in the quotient
  simpa [Nat.add_assoc, he] using h

end GSsupport

namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q] [Finite Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q


def augComapEquivSucc (n : ℕ) :
    (↥((aug p Q ^ (n+2)).comap (aug p Q ^ (n+1)).subtype)) ≃ₗ[k]
       (↥(aug p Q ^ (n+2))) :=
{ toFun := fun x => ⟨(x.1 : B), x.2⟩
  invFun := fun x =>
    ⟨⟨(x.1 : B), pow_antitone_succ p Q n x.2⟩, x.2⟩
  left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro x; apply Subtype.ext; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl }

@[simp] lemma finrank_aug_comap_ss (n : ℕ) :
    Module.finrank k
      (↥((aug p Q ^ (n+2)).comap (aug p Q ^ (n+1)).subtype)) =
      Module.finrank k (↥(aug p Q ^ (n+2))) :=
  LinearEquiv.finrank_eq (augComapEquivSucc p Q n)

/-- Starting at the non-scalar power, powers split into the preceding Hilbert
coefficients and a tail. `Submodule.mul` has `1` equal to the scalar range, not
`⊤`, so the base is `finrank_aug_add_one`, not `finrank_top`. -/
lemma prefix_augCoeffs_add_power (m : ℕ) :
    (∑ i ∈ Finset.range (m+1), augCoeffs p Q i) +
        Module.finrank k (↥(aug p Q ^ (m+1))) =
      Module.finrank k B := by
  classical
  induction m with
  | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        Nat.zero_add]
      -- first coefficient is the scalar `1` quotient
      rw [augCoeffs_zero p Q]
      rw [pow_one]
      rw [finrank_algebra_eq_card p Q]
      simpa [Nat.add_comm] using (finrank_aug_add_one p Q)
  | succ m ih =>
      have hq := Submodule.finrank_quotient_add_finrank
        ((aug p Q ^ (m+2)).comap (aug p Q ^ (m+1)).subtype)
      -- the quotient here is exactly `augLayer (m+1)`
      change augCoeffs p Q (m+1) +
          Module.finrank k
            (↥((aug p Q ^ (m+2)).comap (aug p Q ^ (m+1)).subtype)) =
            Module.finrank k (↥(aug p Q ^ (m+1))) at hq
      rw [finrank_aug_comap_ss p Q m] at hq
      -- adjoining this coefficient to the prefix is harmless arithmetic
      simp only [Finset.sum_range_succ] at ih ⊢
      have ee : m + 1 + 1 = m + 2 := by omega
      rw [ee]
      omega

/-- Removing the deep tail from the previous inequality yields its familiar
prefix-Hilbert form.  This is intentionally cumulative. -/
lemma prefix_kernelLayer_le_coeffs (hp : IsPGroup p Q)
    (T : Finset Q) (m : ℕ)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    (∑ i ∈ Finset.range (m+1), Module.finrank k (kernelLayer p Q T i)) ≤
      rnum p Q T * (∑ i ∈ Finset.range (m+1), augCoeffs p Q i) := by
  have h := prefix_kernelLayer_estimate p Q hp T m hcard hspan
  have ha := prefix_augCoeffs_add_power p Q m
  -- distribute the multiplication after substituting the splitting of the
  -- algebra dimension.
  rw [← ha, Nat.mul_add] at h
  omega

end GSsupport

namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q] [Finite Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

lemma kernelLayer_add_nextCoeff (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (i : ℕ) :
    Module.finrank k (kernelLayer p Q T i) + augCoeffs p Q (i+2) =
      T.card * augCoeffs p Q (i+1) := by
  have hk := finrank_kernelLayer p Q T i
  have hc := coefficient_kernel_drop p Q T hleft i
  omega

lemma prefix_layers_add_coeff (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) (m : ℕ) :
    (∑ i ∈ Finset.range (m+1), Module.finrank k (kernelLayer p Q T i)) +
      (∑ i ∈ Finset.range (m+1), augCoeffs p Q (i+2)) =
        T.card * (∑ i ∈ Finset.range (m+1), augCoeffs p Q (i+1)) := by
  classical
  induction m with
  | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
      simpa using (kernelLayer_add_nextCoeff p Q T hleft 0)
  | succ m ih =>
      have he := kernelLayer_add_nextCoeff p Q T hleft (m+1)
      simp only [Finset.sum_range_succ] at ih ⊢
      -- distribute the right multiplication over the last summand
      rw [Nat.mul_add]
      omega

lemma prefix_coefficient_recurrence (hp : IsPGroup p Q)
    (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤)
    (m : ℕ) :
    T.card * (∑ i ∈ Finset.range (m+1), augCoeffs p Q (i+1)) ≤
      (∑ i ∈ Finset.range (m+1), augCoeffs p Q (i+2)) +
        rnum p Q T * (∑ i ∈ Finset.range (m+1), augCoeffs p Q i) := by
  have he := prefix_layers_add_coeff p Q T hleft m
  have hb := prefix_kernelLayer_le_coeffs p Q hp T m hcard hspan
  omega
end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/Cumulative.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/MinimalBound.lean
section
open CategoryTheory
noncomputable section
open scoped BigOperators
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q

/-- With all group elements as generators the elementary presentation is of course onto J. -/
lemma aug_le_genLeft_univ [Fintype Q] :
  aug p Q ≤ genLeft p Q (Finset.univ : Finset Q) := by
  classical
  intro x hx
  have hone (q : Q) : delta p Q q ∈ genLeft p Q (Finset.univ : Finset Q) := by
    rw [← relMap_range (p:=p) (Q:=Q)]
    let t : (↥(Finset.univ : Finset Q)) := ⟨q, Finset.mem_univ _⟩
    exact ⟨basisVec p Q (Finset.univ) t, relMap_basisVec p Q _ t⟩
  have hzero : eps p Q x = 0 := hx
  have heq : x.sum (fun q c => c • delta p Q q) = x := by
    rw [sum_delta (p:=p) (Q:=Q), hzero]
    simp
  rw [← heq]
  -- expand the finite support sum; each generator is in the left ideal
  classical
  exact Submodule.sum_mem _ (fun i hi =>
    (genLeft p Q (Finset.univ : Finset Q)).smul_mem (x i) (hone i))

end GSsupport

namespace GSsupport
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable (p : ℕ) [Fact p.Prime] (Q : Type*) [Group Q]
local notation "k" => ZMod p
local notation "B" => MonoidAlgebra (ZMod p) Q
variable [Finite Q]

-- The free bar term with all group elements.
local notation "U" => (Finset.univ : Finset Q)

/-- Substitute the preferred lifts in a vector with all group coordinates. -/
def allLift [Fintype Q] (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T) :
    relFree p Q (Finset.univ : Finset Q) →ₗ[k] relFree p Q T := by
  classical
  exact
  { toFun := fun w => ∑ i : (↥(Finset.univ : Finset Q)),
        vecMul p Q T (w i) (genLiftVec p Q T hleft i.1)
    map_add' := by
      intro x y
      simp only [Pi.add_apply]
      simp_rw [vecMul_add]
      exact Finset.sum_add_distrib
    map_smul' := by
      intro c x
      -- scalar is central in the group algebra
      simp only [Pi.smul_apply, RingHom.id_apply]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      funext j
      change (c • x i) * genLiftVec p Q T hleft i.1 j =
        (c • (x i * genLiftVec p Q T hleft i.1 j))
      simp }

lemma relMap_allLift [Fintype Q] (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (w : relFree p Q (Finset.univ : Finset Q)) :
    relMap p Q T (allLift p Q T hleft w) =
      relMap p Q (Finset.univ : Finset Q) w := by
  classical
  change relMap p Q T
    (∑ i : (↥(Finset.univ : Finset Q)),
        vecMul p Q T (w i) (genLiftVec p Q T hleft i.1)) = _
  rw [map_sum]
  change (∑ i : (↥(Finset.univ : Finset Q)),
      relMap p Q T (vecMul p Q T (w i) (genLiftVec p Q T hleft i.1))) = _
  simp_rw [relMap_mul, relMap_genLiftVec]
  rfl

lemma allLift_basis [Fintype Q] (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (i : (↥(Finset.univ : Finset Q))) :
    allLift p Q T hleft (basisVec p Q (Finset.univ : Finset Q) i) =
      genLiftVec p Q T hleft i.1 := by
  classical
  change (∑ j : (↥(Finset.univ : Finset Q)),
     vecMul p Q T (basisVec p Q (Finset.univ : Finset Q) i j)
       (genLiftVec p Q T hleft j.1)) = _
  classical
  rw [Finset.sum_eq_single i]
  · simp [basisVec]
    funext j
    simp [vecMul]
  · intro b hb hne
    simp [basisVec, hne]
    funext j
    simp [vecMul]
  · simp

lemma allLift_vecMul [Fintype Q] (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (a : B) (w : relFree p Q (Finset.univ : Finset Q)) :
    allLift p Q T hleft (vecMul p Q (Finset.univ : Finset Q) a w) =
       vecMul p Q T a (allLift p Q T hleft w) := by
  classical
  -- it is just distribution of left multiplication over a finite sum
  change (∑ i : (↥(Finset.univ : Finset Q)),
      vecMul p Q T (a * w i) (genLiftVec p Q T hleft i.1)) = _
  change (∑ i : (↥(Finset.univ : Finset Q)),
      vecMul p Q T (a * w i) (genLiftVec p Q T hleft i.1)) =
      vecMul p Q T a
        (∑ i : (↥(Finset.univ : Finset Q)),
          vecMul p Q T (w i) (genLiftVec p Q T hleft i.1))
  -- pointwise to avoid a module algebra instance on tuples
  funext j
  simp [vecMul, Finset.mul_sum, mul_assoc]

lemma allLift_bar [Fintype Q] (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (q r : Q) :
    allLift p Q T hleft
      (barRelation p Q (Finset.univ : Finset Q)
        (aug_le_genLeft_univ p Q) q r) =
      barRelation p Q T hleft q r := by
  classical
  let iq : (↥(Finset.univ : Finset Q)) := ⟨q, Finset.mem_univ _⟩
  let ir : (↥(Finset.univ : Finset Q)) := ⟨r, Finset.mem_univ _⟩
  let iqr : (↥(Finset.univ : Finset Q)) := ⟨q*r, Finset.mem_univ _⟩
  -- on the universal set the chosen lifts are its standard vectors
  have hs (x : Q) : genLiftVec p Q (Finset.univ : Finset Q)
        (aug_le_genLeft_univ p Q) x =
      basisVec p Q (Finset.univ : Finset Q) ⟨x, Finset.mem_univ _⟩ :=
    by
      simpa using (genLiftVec_selected p Q (Finset.univ : Finset Q)
        (aug_le_genLeft_univ p Q)
        (⟨x, Finset.mem_univ _⟩ : (↥(Finset.univ : Finset Q))))
  -- expand the three terms and use linearity
  unfold barRelation
  rw [map_sub, map_add]
  rw [hs q, hs r, hs (q*r)]
  -- map of the multiplied basis
  rw [allLift_vecMul]
  simp [allLift_basis, iq, ir, iqr]

/-- The value of a raw one-cochain on the all-generators bar term. -/
def allValue [Fintype Q] (v : Q → k) :
    relFree p Q (Finset.univ : Finset Q) →ₗ[k] k := by
  classical
  exact
  { toFun := fun w => ∑ i : (↥(Finset.univ : Finset Q)),
        (eps p Q (w i)) * v i.1
    map_add' := by
      intro x y
      simp only [Pi.add_apply, map_add, add_mul]
      rw [Finset.sum_add_distrib]
    map_smul' := by
      intro c x
      simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp [mul_assoc] }

lemma allValue_basis [Fintype Q] (v : Q → k)
    (i : (↥(Finset.univ : Finset Q))) :
    allValue p Q v (basisVec p Q (Finset.univ : Finset Q) i) = v i.1 := by
  classical
  change (∑ j : (↥(Finset.univ : Finset Q)),
      eps p Q (basisVec p Q (Finset.univ : Finset Q) i j) * v j.1) = _
  simp [basisVec]

lemma allValue_vecMul [Fintype Q] (v : Q → k) (a : B)
    (w : relFree p Q (Finset.univ : Finset Q)) :
    allValue p Q v (vecMul p Q (Finset.univ : Finset Q) a w) =
      (eps p Q a) * allValue p Q v w := by
  classical
  change (∑ i : (↥(Finset.univ : Finset Q)),
      eps p Q (a * w i) * v i.1) = _
  simp only [map_mul]
  -- distribute the common augmentation scalar
  conv_rhs =>
    change (eps p Q a) * (∑ i : (↥(Finset.univ : Finset Q)), eps p Q (w i) * v i.1)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc]

lemma allValue_gen [Fintype Q] (v : Q → k) (q : Q) :
    allValue p Q v
      (genLiftVec p Q (Finset.univ : Finset Q)
        (aug_le_genLeft_univ p Q) q) = v q := by
  classical
  rw [show genLiftVec p Q (Finset.univ : Finset Q)
        (aug_le_genLeft_univ p Q) q =
        basisVec p Q (Finset.univ : Finset Q)
          (⟨q, Finset.mem_univ _⟩ : (↥(Finset.univ : Finset Q))) by
      simpa using (genLiftVec_selected p Q (Finset.univ : Finset Q)
        (aug_le_genLeft_univ p Q)
        (⟨q, Finset.mem_univ _⟩ : (↥(Finset.univ : Finset Q))))]
  simpa using
    (allValue_basis p Q v (⟨q, Finset.mem_univ _⟩ : (↥(Finset.univ : Finset Q))))

lemma allValue_bar [Fintype Q] (v : Q → k) (q r : Q) :
    allValue p Q v
      (barRelation p Q (Finset.univ : Finset Q)
        (aug_le_genLeft_univ p Q) q r) = v q + v r - v (q*r) := by
  classical
  unfold barRelation
  rw [map_sub, map_add]
  rw [allValue_gen, allValue_gen, allValue_vecMul, allValue_gen]
  rw [eps_of]
  simp
  -- eps of a group element is one
  -- simp should handle eps_of

/-- A coboundary amongst the explicit minimal-relation bars is zero.  This is
 the algebraic injectivity input: the first arrow of a minimal presentation has
all its kernel coordinates in J. -/
lemma minFunc_zero_of_boundary [TopologicalSpace Q] [IsTopologicalGroup Q]
    [DiscreteTopology Q]
    (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤)
    (l : Module.Dual k (minimalRel p Q T))
    (v : Q → k)
    (hv : ∀ q r : Q,
      relCocycle p Q T hleft l q r = v r - v (q*r) + v q) :
    l = 0 := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  let U0 : Finset Q := Finset.univ
  let hU : aug p Q ≤ genLeft p Q (Finset.univ : Finset Q) :=
    aug_le_genLeft_univ p Q
  let W : Submodule k (relFree p Q (Finset.univ : Finset Q)) :=
    Submodule.span k (Set.range
      (fun z : Q × (↥(Finset.univ : Finset Q)) =>
         barRelation p Q (Finset.univ : Finset Q) hU z.1 z.2.1))
  have Wker (w : relFree p Q (Finset.univ : Finset Q)) (hw : w ∈ W) :
      relMap p Q (Finset.univ : Finset Q) w = 0 := by
    -- every spanning bar is a relation
    refine Submodule.span_induction (p:= fun x (_ : x ∈ W) =>
      relMap p Q (Finset.univ : Finset Q) x = 0) ?_ ?_ ?_ ?_ hw
    · intro x hx
      obtain ⟨z, rfl⟩ := hx
      exact relMap_barRelation p Q _ hU _ _
    · simp
    · intro x y hx hy ex ey
      simp [ex, ey]
    · intro c x hx ex
      simp [ex]
  -- equality of the two functionals on the universal relation module
  have compare (w : relFree p Q (Finset.univ : Finset Q))
      (hw : w ∈ W) :
      allValue p Q v w =
        minFunc p Q T l
          (⟨allLift p Q T hleft w,
            (LinearMap.mem_ker).2
              (by rw [relMap_allLift]; exact Wker w hw)⟩ : relSub p Q T) := by
    -- span induction; proof arguments of the subtypes are irrelevant
    refine Submodule.span_induction (p:= fun x (hx : x ∈ W) =>
      allValue p Q v x =
        minFunc p Q T l
          (⟨allLift p Q T hleft x,
            (LinearMap.mem_ker).2
              (by rw [relMap_allLift]; exact Wker x hx)⟩ : relSub p Q T)) ?_ ?_ ?_ ?_ hw
    · intro x hx
      obtain ⟨z, rfl⟩ := hx
      rcases z with ⟨q,r⟩
      rw [allValue_bar]
      -- substitute the lift of the universal two bar
      have heqsub :
          (⟨allLift p Q T hleft
              (barRelation p Q (Finset.univ : Finset Q) hU q r.1),
              (LinearMap.mem_ker).2 (by
                rw [relMap_allLift]
                exact relMap_barRelation p Q (Finset.univ : Finset Q) hU q r.1)⟩ : relSub p Q T) =
          (⟨barRelation p Q T hleft q r.1,
              (LinearMap.mem_ker).2 (relMap_barRelation p Q T hleft q r.1)⟩ : relSub p Q T) := by
            apply Subtype.ext
            exact allLift_bar p Q T hleft q r.1
      rw [heqsub]
      change _ = relCocycle p Q T hleft l q r.1
      rw [hv q r.1]
      abel
    · change (allValue p Q v) 0 = _
      rw [map_zero]
      have heqsub :
          (⟨allLift p Q T hleft 0,
            (LinearMap.mem_ker).2 (by simp)⟩ : relSub p Q T) = 0 := by
            apply Subtype.ext
            exact map_zero _
      rw [heqsub, map_zero]
    · intro x y hx hy ex ey
      calc
        (allValue p Q v) (x+y) =
          (allValue p Q v) x + (allValue p Q v) y := map_add _ _ _
        _ = (minFunc p Q T l)
              (⟨allLift p Q T hleft x, _⟩ : relSub p Q T) +
            (minFunc p Q T l)
              (⟨allLift p Q T hleft y, _⟩ : relSub p Q T) := by rw [ex, ey]
        _ = (minFunc p Q T l)
              ((⟨allLift p Q T hleft x, _⟩ : relSub p Q T) +
               (⟨allLift p Q T hleft y, _⟩ : relSub p Q T)) := (map_add _ _ _).symm
        _ = _ := by
          congr 1
          apply Subtype.ext
          exact (map_add (allLift p Q T hleft) x y).symm
    · intro c x hx ex
      calc
        (allValue p Q v) (c • x) = c • (allValue p Q v) x := map_smul _ _ _
        _ = c • (minFunc p Q T l)
              (⟨allLift p Q T hleft x, _⟩ : relSub p Q T) := by rw [ex]
        _ = (minFunc p Q T l)
             (c • (⟨allLift p Q T hleft x, _⟩ : relSub p Q T)) := (map_smul _ _ _).symm
        _ = _ := by
          congr 1
          apply Subtype.ext
          exact (map_smul (allLift p Q T hleft) c x).symm
  -- every universal relation is in this span
  have inW (w : relFree p Q (Finset.univ : Finset Q))
      (hw : relMap p Q (Finset.univ : Finset Q) w = 0) : w ∈ W := by
    exact kernel_span_bars p Q (Finset.univ : Finset Q) hU w hw
  -- now a relation in the minimal presentation.  Insert it in the universal
  -- bar term by using the same coefficients at its selected coordinates.
  have vanishes (u : relSub p Q T) : minFunc p Q T l u = 0 := by
    let emb : relFree p Q (Finset.univ : Finset Q) :=
      ∑ t : (↥T), vecMul p Q (Finset.univ : Finset Q) (u.1 t)
        (basisVec p Q (Finset.univ : Finset Q)
          (⟨t.1, Finset.mem_univ _⟩ : (↥(Finset.univ : Finset Q))))
    have lift_emb : allLift p Q T hleft emb = (u.1 : relFree p Q T) := by
      dsimp [emb]
      rw [map_sum]
      -- multiplied bases go to multiplied chosen lifts
      simp_rw [allLift_vecMul, allLift_basis]
      simp_rw [genLiftVec_selected]
      exact (vec_sum p Q T u.1).symm
    have embker : relMap p Q (Finset.univ : Finset Q) emb = 0 := by
      rw [← relMap_allLift (p:=p) (Q:=Q) T hleft, lift_emb]
      exact LinearMap.mem_ker.1 u.2
    have eval0 : allValue p Q v emb = 0 := by
      dsimp [emb]
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro t ht
      rw [allValue_vecMul, allValue_basis]
      have hz : eps p Q (u.1 t) = 0 := by
        exact relKernel_coordinates p Q T hcard hspan u.1
          (LinearMap.mem_ker.1 u.2) t
      simp [hz]
    have eqn := compare emb (inW emb embker)
    rw [eval0] at eqn
    -- forget the chosen proofs in the lifted subtype
    have same :
        (⟨allLift p Q T hleft emb,
            (LinearMap.mem_ker).2
              (by rw [relMap_allLift]; exact Wker emb (inW emb embker))⟩ : relSub p Q T) = u := by
      apply Subtype.ext
      exact lift_emb
    rw [same] at eqn
    exact eqn.symm
  -- the quotient map from relations onto minimal relations is onto
  apply LinearMap.ext
  intro z
  obtain ⟨u, rfl⟩ :=
    (Submodule.mkQ_surjective
      ((augRel p Q T).comap (relSub p Q T).subtype)) z
  have hz := vanishes u
  change l ((Submodule.mkQ _) u) = (0 : Module.Dual k (minimalRel p Q T)) ((Submodule.mkQ _) u)
  simpa [minFunc] using hz

end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/MinimalBound.lean

-- BEGIN INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/HeadBound.lean
section
open CategoryTheory CategoryTheory.Limits Functor ContinuousMap
open ContinuousCohomology
noncomputable section
namespace GSsupport
attribute [local instance] Classical.propDecidable
variable (p : ℕ) [Fact p.Prime] (Q : Type) [Group Q]
 [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
local notation "k" => ZMod p

-- the short complex at degree two, named to keep the concrete homology readable
abbrev twoSC := (discHC p Q).sc 2

/-- The incoming map to the literal kernel of `d_{23}`. -/
noncomputable def twoF : (twoSC p Q).X₁ ⟶ TopModuleCat.ker (twoSC p Q).g :=
  (TopModuleCat.isLimitKer ((twoSC p Q).g)).lift
     (KernelFork.ofι (twoSC p Q).f (twoSC p Q).zero)

/-- The elementary left homology datum: cycles are the literal kernel and
classes the literal quotient by the incoming map. -/
noncomputable def twoLeft : (twoSC p Q).LeftHomologyData := by
  let S := twoSC p Q
  exact
  { K := TopModuleCat.ker S.g
    H := TopModuleCat.coker (twoF p Q)
    i := TopModuleCat.kerι S.g
    π := TopModuleCat.cokerπ (twoF p Q)
    wi := TopModuleCat.kerι_comp _
    hi := TopModuleCat.isLimitKer _
    wπ := by
      change (twoF p Q) ≫ TopModuleCat.cokerπ (twoF p Q) = 0
      simpa using (TopModuleCat.comp_cokerπ (twoF p Q))
    hπ := TopModuleCat.isColimitCoker _ }

/-- the bar assignment is linear in the functional. -/
def relHomLM (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T) :
    Module.Dual k (minimalRel p Q T) →ₗ[k] (discHC p Q).X 2 where
  toFun l := relAsHomogeneous p Q T hleft l
  map_add' l l' := by
    apply Subtype.ext
    apply ContinuousMap.ext; intro a
    apply ContinuousMap.ext; intro b
    apply ContinuousMap.ext; intro c
    change ((l + l') : Module.Dual k _) _ = (l _ : k) + (l' _ : k)
    rfl
  map_smul' z l := by
    apply Subtype.ext
    apply ContinuousMap.ext; intro a
    apply ContinuousMap.ext; intro b
    apply ContinuousMap.ext; intro c
    change ((z • l) : Module.Dual k _) _ = z * (l _ : k)
    rfl


/-- Incoming map to the literal `d 2 3` kernel, without the noncomputable
`next` of `ComplexShape`. This concrete object is often simpler than `sc`. -/
noncomputable def expF : (discHC p Q).X 1 ⟶ TopModuleCat.ker ((discHC p Q).d 2 3) :=
  (TopModuleCat.isLimitKer ((discHC p Q).d 2 3)).lift
    (KernelFork.ofι ((discHC p Q).d 1 2)
      ((discHC p Q).d_comp_d 1 2 3))

/-- Literal cycles supplied by the relation bars. -/
def relKerExpLM (T : Finset Q) (hleft : aug p Q ≤ genLeft p Q T) :
    Module.Dual k (minimalRel p Q T) →ₗ[k]
      (TopModuleCat.ker ((discHC p Q).d 2 3)) where
  toFun l := ⟨relAsHomogeneous p Q T hleft l,
    relAsHomogeneous_is_cocycle p Q T hleft l⟩
  map_add' l l' := by
    apply Subtype.ext
    exact (relHomLM p Q T hleft).map_add l l'
  map_smul' z l := by
    apply Subtype.ext
    exact (relHomLM p Q T hleft).map_smul z l

/-- Concrete, literal quotient cycles/boundaries. -/
abbrev expH := TopModuleCat.coker (expF p Q)
noncomputable def relClassExp (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T) :
    Module.Dual k (minimalRel p Q T) →ₗ[k] (expH p Q) :=
  ((TopModuleCat.cokerπ (expF p Q)).hom.toLinearMap).comp
     (relKerExpLM p Q T hleft)

lemma relClassExp_inj [Finite Q] (T : Finset Q)
    (hleft : aug p Q ≤ genLeft p Q T)
    (hcard : T.card = Module.finrank k (oneLayer p Q))
    (hspan : Submodule.span k ((delta1 p Q) '' (↑T : Set Q)) = ⊤) :
    Function.Injective (relClassExp p Q T hleft) := by
  classical
  intro l l' eqll
  -- suffice to kill a class with value zero
  have hz : relClassExp p Q T hleft (l-l') = 0 := by
    rw [map_sub (relClassExp p Q T hleft), sub_eq_zero]
    exact eqll
  -- in the concrete quotient zero means membership in the incoming range
  have hmem : (relKerExpLM p Q T hleft (l-l') :
        (TopModuleCat.ker ((discHC p Q).d 2 3))) ∈
      (expF p Q).hom.range := by
    -- `mkQ` zero precisely on the defining submodule
    exact (Submodule.Quotient.mk_eq_zero _).1 hz
  obtain ⟨A, hA⟩ := hmem
  have he : ((discHC p Q).d 1 2).hom A =
        relAsHomogeneous p Q T hleft (l-l') := by
    -- forget the kernel lift
    have hv := congrArg (fun z : TopModuleCat.ker ((discHC p Q).d 2 3) => z.1) hA
    exact hv
  have hzero : l-l' = 0 := by
    have hb : ∃ A : (discHC p Q).X 1,
        ((discHC p Q).d 1 2).hom A =
          relAsHomogeneous p Q T hleft (l-l') := ⟨A, he⟩
    obtain ⟨v, hv⟩ := (boundary_iff_unhomog p Q
      (relAsHomogeneous p Q T hleft (l-l'))).1 hb
    apply minFunc_zero_of_boundary p Q T hleft hcard hspan (l-l') v
    intro q r
    simpa [unhomog_relAsHomogeneous] using hv q r
  exact sub_eq_zero.mp hzero

end GSsupport

namespace GSsupport
open CategoryTheory CategoryTheory.Limits
open ContinuousCohomology
noncomputable section
variable (p : ℕ) [Fact p.Prime] (Q : Type) [Group Q]
 [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
local notation "k" => ZMod p
abbrev expSC := (discHC p Q).sc' 1 2 3
noncomputable def expLeft : (expSC p Q).LeftHomologyData where
 K := TopModuleCat.ker (expSC p Q).g
 H := TopModuleCat.coker (expF p Q)
 i := TopModuleCat.kerι _
 π := TopModuleCat.cokerπ _
 wi := TopModuleCat.kerι_comp _
 hi := TopModuleCat.isLimitKer _
 wπ := by
  change expF p Q ≫ TopModuleCat.cokerπ (expF p Q) = 0
  exact TopModuleCat.comp_cokerπ _
 hπ := TopModuleCat.isColimitCoker _

noncomputable def isoLE {A B : TopModuleCat k} (e : A ≅ B) :
    A ≃ₗ[k] B :=
  LinearEquiv.ofBijective e.hom.hom.toLinearMap
    ⟨by
      intro x y h
      have hh := congrArg (fun z => e.inv z) h
      simpa using hh,
     by
      intro y
      refine ⟨e.inv y, ?_⟩
      simpa using congrArg (fun m => m) (rfl : (e.hom (e.inv y)) = _)⟩

end
end GSsupport

end

end
-- END INLINED FILE: Mathlib/Support/golod_shafarevich_inequality_8495fc81e8/HeadBound.lean

-- BEGIN INLINED MAIN PRELUDE
set_option maxHeartbeats 4000000

open LeanEval.GroupTheory
open CategoryTheory
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem golod_shafarevich_inequality (p : ℕ) [Fact p.Prime] (Q : Type)
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [DiscreteTopology Q] [Finite Q] :
    IsPGroup p Q → Nontrivial Q →
      (generatorRank Q : ℝ) ^ 2 < 4 * (relationRank p Q : ℝ) :=
/-ResultProofBegin-/by
  classical
  intro hp hnon
  letI : Nontrivial Q := hnon
  have hdN : 0 < generatorRank Q := GSsupport.my_generator_rank_pos Q
  -- A minimal first algebra presentation of the augmentation ideal.
  obtain ⟨T, hTle, hTspan⟩ := GSsupport.small_span p Q
  have hbase := GSsupport.base_step p Q T hTspan
  have hleft := GSsupport.J_le_left p Q T hbase hp
  have hTrange : Set.range (fun t : ↥T => GSsupport.delta1 p Q t.1) =
        (GSsupport.delta1 p Q) '' (↑T : Set Q) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.1, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have hdimle : Module.finrank (ZMod p) (GSsupport.oneLayer p Q) ≤ T.card := by
    have htmp := finrank_le_of_span_eq_top (R := ZMod p)
      (v := fun t : ↥T => GSsupport.delta1 p Q t.1)
    have hh : Submodule.span (ZMod p)
        (Set.range (fun t : ↥T => GSsupport.delta1 p Q t.1)) = ⊤ := by
      rw [hTrange, hTspan]
    simpa using htmp hh
  have hTcard' : T.card = Module.finrank (ZMod p) (GSsupport.oneLayer p Q) :=
    Nat.le_antisymm hTle hdimle
  -- This chosen set really generates the group (Burnside's argument with the
  -- coset module), hence dominates the trusted minimal generator rank.
  have hg : Subgroup.closure (T : Set Q) = ⊤ :=
    GSsupport.closure_of_J_le_left p Q T hleft
  have hdT : generatorRank Q ≤ T.card := by
    unfold generatorRank
    apply Nat.sInf_le
    refine ⟨T, rfl, ?_⟩
    simpa [GSsupport.tclose_eq Q] using hg
  have hrelhead : Module.finrank (ZMod p) (GSsupport.minimalRel p Q T) ≤
        relationRank p Q := by
    let un2 : ((GSsupport.discHC p Q).X 2) →ₗ[ZMod p]
          (Q → Q → ZMod p) :=
      { toFun := fun F => GSsupport.unhomogTwo p Q F
        map_add' := by
          intro F G
          rfl
        map_smul' := by
          intro z F
          rfl }
    have un2inj : Function.Injective un2 := by
      intro F G h
      have hh := congrArg
        (fun f : Q → Q → ZMod p => GSsupport.asInvTwo p Q f) h
      change GSsupport.asInvTwo p Q (GSsupport.unhomogTwo p Q F) =
        GSsupport.asInvTwo p Q (GSsupport.unhomogTwo p Q G) at hh
      simpa only [GSsupport.homogTwo_unhomog] using hh
    -- Finite `Q` makes the (dehomogenized) two cochains a finite product.
    -- Evaluation above is injective even on all invariant cochains, hence
    -- all the concrete kernels and their cokernels are finite-dimensional.
    letI : Module.Finite (ZMod p) ((GSsupport.discHC p Q).X 2) := by
      apply Module.Finite.of_injective un2
      exact un2inj
    letI : Module.Finite (ZMod p) (GSsupport.expH p Q) := by
      infer_instance
    have hle : Module.finrank (ZMod p)
            (Module.Dual (ZMod p) (GSsupport.minimalRel p Q T)) ≤
            Module.finrank (ZMod p) (GSsupport.expH p Q) := by
      apply LinearMap.finrank_le_finrank_of_injective
        (f := GSsupport.relClassExp p Q T hleft)
      exact GSsupport.relClassExp_inj p Q T hleft hTcard' hTspan
    let K := GSsupport.discHC p Q
    have hi : (ComplexShape.up ℕ).prev (2 : ℕ) = 1 := by
      norm_num
    have hnext : (ComplexShape.up ℕ).next (2 : ℕ) = 3 := by
      norm_num
    let esc := HomologicalComplex.isoSc' K 1 2 3 hi hnext
    let ehom : (K.sc 2).homology ≅ (K.sc' 1 2 3).homology :=
      ShortComplex.homologyMapIso esc
    let eleft : (K.sc' 1 2 3).homology ≅ GSsupport.expH p Q :=
      (GSsupport.expLeft p Q).homologyIso
    -- Unfolding `continuousCohomology` here is definitional: it is the
    -- homology functor on `homogeneousCochains`.  Thus the following
    -- isomorphism lands in the very object of `relationRank`.
    let ee :
        ((continuousCohomology (ZMod p) Q 2).obj
           (GSsupport.discTrivRep p Q)) ≅ GSsupport.expH p Q :=
      ehom ≪≫ eleft
    have heq : Module.finrank (ZMod p) (GSsupport.expH p Q) =
        Module.finrank (ZMod p)
           ((continuousCohomology (ZMod p) Q 2).obj
             (GSsupport.discTrivRep p Q)) :=
      (LinearEquiv.finrank_eq (GSsupport.isoLE p ee)).symm
    change Module.finrank (ZMod p) (GSsupport.minimalRel p Q T) ≤
        Module.finrank (ZMod p)
          ((continuousCohomology (ZMod p) Q 2).obj
            (GSsupport.discTrivRep p Q))
    calc
      Module.finrank (ZMod p) (GSsupport.minimalRel p Q T) =
          Module.finrank (ZMod p)
             (Module.Dual (ZMod p) (GSsupport.minimalRel p Q T)) :=
        (Subspace.dual_finrank_eq).symm
      _ ≤ Module.finrank (ZMod p) (GSsupport.expH p Q) := hle
      _ = _ := heq
  have hrnum : GSsupport.rnum p Q T ≤ relationRank p Q := by
    simpa [GSsupport.rnum] using hrelhead
  -- Nakayama on the *whole* relation space and the intersection filtration
  -- give an honest prefix inequality.  This avoids claiming strictness for a
  -- single translated layer: in general `R ∩ J^s F = J^{s-1}R` is false.
  have hprefix (m : ℕ) :
      T.card * (∑ i ∈ Finset.range (m+1), GSsupport.augCoeffs p Q (i+1)) ≤
        (∑ i ∈ Finset.range (m+1), GSsupport.augCoeffs p Q (i+2)) +
          relationRank p Q *
            (∑ i ∈ Finset.range (m+1), GSsupport.augCoeffs p Q i) := by
    have hh := GSsupport.prefix_coefficient_recurrence
      p Q hp T hleft hTcard' hTspan m
    exact hh.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ hrnum)
      (∑ i ∈ Finset.range (m+1), GSsupport.augCoeffs p Q (i+2)))
  have ha1 : GSsupport.augCoeffs p Q 1 = T.card :=
    (GSsupport.augCoeffs_one_eq p Q).trans hTcard'.symm
  have hvan : ∃ N : ℕ, ∀ n ≥ N, GSsupport.augCoeffs p Q n = 0 :=
    GSsupport.aug_zero_above p Q hp
  have hTpos : 0 < T.card := lt_of_lt_of_le hdN hdT
  by_cases hsmall : T.card = 1
  · -- In the one-column case a residue relation already has dimension one;
    -- this also follows from finite Nakayama and the total rank of the
    -- presentation.
    have htotal := GSsupport.finrank_relSub_add p Q T hleft
    have hgen := GSsupport.finrank_relSub_le_top_mul_card p Q hp T
    have hau := GSsupport.finrank_aug_add_one p Q
    have hTopge : T.card ≤
        Module.finrank (ZMod p) (GSsupport.minimalRel p Q T) := by
      have arith (d q s R r : ℕ) (hq : 0 < q)
          (hs : s + 1 = q) (he : s + R = d*q)
          (hl : R ≤ r*q) : d ≤ r := by
        by_contra hbad
        have dr : r + 1 ≤ d := by omega
        have mm : (r+1)*q ≤ d*q := Nat.mul_le_mul_right q dr
        rw [he.symm] at mm
        have slt : s < q := by omega
        have biglt : s + R < (r+1)*q := by
          rw [Nat.add_mul]
          simp only [one_mul]
          omega
        exact (Nat.not_lt_of_ge mm) biglt
      exact arith T.card (Nat.card Q)
        (Module.finrank (ZMod p) (↥(GSsupport.aug p Q)))
        (Module.finrank (ZMod p) (GSsupport.relSub p Q T))
        (Module.finrank (ZMod p) (GSsupport.minimalRel p Q T))
        (Nat.card_pos)
        (by simpa [Nat.add_comm] using hau) htotal hgen
    have hr1 : 1 ≤ relationRank p Q := by
      have hx := hTopge.trans hrelhead
      simpa [hsmall] using hx
    have hd1 : generatorRank Q = 1 := by omega
    have hr1r : (1:ℝ) ≤ (relationRank p Q : ℝ) := by exact_mod_cast hr1
    norm_num [hd1]
    linarith
  · have htwo : 2 ≤ T.card := by omega
    have hnum := numerical_gs_prefix_nat T.card (relationRank p Q) htwo
      (GSsupport.augCoeffs p Q) (GSsupport.augCoeffs_zero p Q) ha1 hvan hprefix
    have hc : (generatorRank Q : ℝ) ≤ (T.card : ℝ) := by
      exact_mod_cast hdT
    have hz : (0:ℝ) ≤ (generatorRank Q : ℝ) := by positivity
    nlinarith

/-ResultProofEnd-/
/-ResultEnd-/

end Submission
