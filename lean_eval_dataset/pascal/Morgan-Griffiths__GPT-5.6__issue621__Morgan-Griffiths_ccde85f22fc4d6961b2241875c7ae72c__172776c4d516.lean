import ChallengeDeps
import Submission.Helpers

open LeanEval.Geometry.PascalPappus
open Matrix

namespace Submission

/-ResultProofDefinitionsBegin-/
noncomputable section
local notation "br[" a "," b "," c "]" => a ⬝ᵥ (b ⨯₃ c)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 800000 in
lemma stdid (x y z X Y Z U V W: ℝ) :
 let a : Fin 3 → ℝ := ![1,0,0]
 let b : Fin 3 → ℝ := ![0,1,0]
 let c : Fin 3 → ℝ := ![0,0,1]
 let u : Fin 3 → ℝ := ![x,y,z]
 let v : Fin 3 → ℝ := ![X,Y,Z]
 let w : Fin 3 → ℝ := ![U,V,W]
 (((a ⨯₃ v) ⨯₃ (b ⨯₃ u)) ⬝ᵥ
             (((a ⨯₃ w) ⨯₃ (c ⨯₃ u)) ⨯₃
              ((b ⨯₃ w) ⨯₃ (c ⨯₃ v)))) =
   y*z * (X*Z*U*V - X*Y*U*W) -
   x*z * (Y*Z*U*V - X*Y*V*W) +
   x*y * (Y*Z*U*W - X*Z*V*W) := by
 dsimp
 simp [dotProduct, crossProduct, Fin.sum_univ_succ]
 ring
set_option maxHeartbeats 1000000 in
lemma br_mul (P : Matrix (Fin 3) (Fin 3) ℝ) (a b c : Fin 3 → ℝ) :
 br[P *ᵥ a, P *ᵥ b, P *ᵥ c] = P.det * br[a,b,c] := by
 rw [Matrix.det_fin_three]
 simp [dotProduct, crossProduct, Matrix.mulVec, Fin.sum_univ_succ]
 ring
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma triple (a b c d: Fin 3 → ℝ) :
 (a ⨯₃ b) ⨯₃ (c ⨯₃ d) =
   (br[a,b,d]) • c - (br[a,b,c]) • d := by
 funext i; fin_cases i <;> simp [dotProduct, crossProduct, Fin.sum_univ_succ] <;> ring
-- meet equivariance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma meet_mul (P : Matrix (Fin 3) (Fin 3) ℝ) (a b c d : Fin 3 → ℝ) :
 (((P*ᵥa) ⨯₃ (P*ᵥb)) ⨯₃ ((P*ᵥc) ⨯₃ (P*ᵥd))) =
   P.det • (P *ᵥ ((a ⨯₃ b) ⨯₃ (c ⨯₃ d))) := by
 rw [triple, triple]
 rw [br_mul, br_mul]
 -- linearity mulVec, algebra vector
 -- ext simp
 funext i
 simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
 ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma br_smul (t u v:ℝ) (a b c:Fin 3→ℝ) :
 br[t • a, u • b, v • c] = (t*u*v) * br[a,b,c] := by
 simp [dotProduct, crossProduct, Fin.sum_univ_succ]
 ring
-- whole
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma F_mul (P : Matrix (Fin 3) (Fin 3) ℝ) (a b c u v w : Fin 3 → ℝ) :
 ((((P*ᵥa) ⨯₃ (P*ᵥv)) ⨯₃ ((P*ᵥb) ⨯₃ (P*ᵥu))) ⬝ᵥ
   ((((P*ᵥa) ⨯₃ (P*ᵥw)) ⨯₃ ((P*ᵥc) ⨯₃ (P*ᵥu))) ⨯₃
    (((P*ᵥb) ⨯₃ (P*ᵥw)) ⨯₃ ((P*ᵥc) ⨯₃ (P*ᵥv))))) =
 (P.det)^4 *
 (((a ⨯₃ v) ⨯₃ (b ⨯₃ u)) ⬝ᵥ
   (((a ⨯₃ w) ⨯₃ (c ⨯₃ u)) ⨯₃
    ((b ⨯₃ w) ⨯₃ (c ⨯₃ v)))) := by
 rw [meet_mul P a v b u, meet_mul P a w c u,
     meet_mul P b w c v]
 -- goal dots
 rw [br_smul, br_mul]
 ring
def cols (a b c : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
 fun i j => ![a i, b i, c i] j
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma det_cols (a b c: Fin 3→ℝ) : (cols a b c).det = br[a,b,c] := by
 rw [Matrix.det_fin_three]
 simp [cols, dotProduct, crossProduct, Fin.sum_univ_succ]
 ring
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma gram_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (a b c: Fin 3 → ℝ) (i j : Fin 3) :
 ((cols a b c)ᵀ * M * (cols a b c)) i j =
   (![a,b,c] i) ⬝ᵥ (M *ᵥ (![a,b,c] j)) := by
 have sel : ∀ (i k : Fin 3), (![a,b,c] i) k = ![a k,b k,c k] i := by
  intro ii kk; fin_cases ii <;> fin_cases kk <;> rfl
 simp [Matrix.mul_apply, cols, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, sel]
 ring
set_option maxRecDepth 100000 in
lemma gram_det (M : Matrix (Fin 3) (Fin 3) ℝ)
 (S : Matrix (Fin 3) (Fin 3) ℝ) :
 (Sᵀ * M * S).det = S.det ^ 2 * M.det := by
 rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
 ring
-- local SamePoint
lemma cross_ne (u v:Fin 3→ℝ) (hu:u≠0) (hv:v≠0) (h:¬ SamePoint u v) : u ⨯₃ v ≠ 0 := by
 rw [crossProduct_ne_zero_iff_linearIndependent]
 rw [LinearIndependent.pair_iff' hu]
 intro k eq
 by_cases hk:k=0
 · subst k
   have : v = 0 := by simpa using eq.symm
   exact hv this
 · exact h ⟨k,hk,eq.symm⟩
-- actually eq binder
set_option maxRecDepth 100000 in
lemma bilin_symm (M:Matrix (Fin 3) (Fin 3) ℝ) (hM:M.IsSymm)
 (u v:Fin 3→ℝ) : u ⬝ᵥ (M*ᵥv) = v ⬝ᵥ (M*ᵥu) := by
 have e01 : M 1 0 = M 0 1 := by simpa using congr_fun (congr_fun hM (0:Fin 3)) (1:Fin 3)
 have e02 : M 2 0 = M 0 2 := by simpa using congr_fun (congr_fun hM (0:Fin 3)) (2:Fin 3)
 have e12 : M 2 1 = M 1 2 := by simpa using congr_fun (congr_fun hM (1:Fin 3)) (2:Fin 3)
 simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
 rw [e01,e02,e12]
 ring
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma pair_nonzero (M:Matrix (Fin 3) (Fin 3) ℝ) (hM:M.IsSymm) (hdet:M.det≠0)
 (u v:Fin 3→ℝ) (hu:u≠0) (hv:v≠0) (hns:¬ SamePoint u v)
 (qu:u ⬝ᵥ(M*ᵥu)=0) (qv:v ⬝ᵥ(M*ᵥv)=0) :
 u ⬝ᵥ (M*ᵥv) ≠ 0 := by
 intro hp
 let z : Fin 3 → ℝ := u ⨯₃ v
 have hz : z ≠ 0 := cross_ne u v hu hv hns
 have hdS : (cols u v z).det ≠ 0 := by
  rw [det_cols]
  rw [triple_product_permutation u v z, triple_product_permutation v z u]
  -- goal z ⋅ u×v ≠0
  change z ⬝ᵥ z ≠ 0
  exact mt dotProduct_self_eq_zero.mp hz -- check
 have gm := gram_det M (cols u v z)
 have gm0 : (((cols u v z)ᵀ * M * (cols u v z))).det = 0 := by
  rw [Matrix.det_fin_three]
  -- entries using gram_apply
  rw [gram_apply M u v z, gram_apply M u v z,
      gram_apply M u v z, gram_apply M u v z,
      gram_apply M u v z, gram_apply M u v z,
      gram_apply M u v z, gram_apply M u v z,
      gram_apply M u v z]
  -- this rewrites occurrences with indices inferred? all 9 same lemma
  -- simp indices
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] -- maybe
  simp [qu,qv,hp, bilin_symm M hM v u]
 -- contradiction
 rw [gm0] at gm
 have : (cols u v z).det ^ 2 * M.det ≠ 0 := mul_ne_zero (pow_ne_zero 2 hdS) hdet
 exact this gm.symm
set_option maxRecDepth 100000 in
lemma cols_mul (a b c:Fin 3→ℝ) (x y z:ℝ) :
 cols a b c *ᵥ ![x,y,z] = x • a + y • b + z • c := by
 funext i
 simp [cols, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
 ring
-- for inverse action on columns
set_option maxRecDepth 100000 in
lemma inv_col (a b c:Fin 3→ℝ) (hn:(cols a b c).det ≠ 0) :
 (cols a b c)⁻¹ *ᵥ a = ![(1:ℝ),0,0] ∧
 (cols a b c)⁻¹ *ᵥ b = ![0,(1:ℝ),0] ∧
 (cols a b c)⁻¹ *ᵥ c = ![0,0,(1:ℝ)] := by
 let S := cols a b c
 have unit : IsUnit S.det := isUnit_iff_ne_zero.mpr hn
 have mul := Matrix.nonsing_inv_mul S unit
 -- apply mulVec standard basis maybe
 have hcol1 : S *ᵥ ![(1:ℝ),0,0] = a := by
   rw [cols_mul]; funext i; simp
 have hcol2 : S *ᵥ ![0,(1:ℝ),0] = b := by
   rw [cols_mul]; funext i; simp
 have hcol3 : S *ᵥ ![0,0,(1:ℝ)] = c := by
   rw [cols_mul]; funext i; simp
 have go (t:Fin 3→ℝ) : S⁻¹ *ᵥ (S *ᵥ t) = t := by
   rw [Matrix.mulVec_mulVec, mul, Matrix.one_mulVec]
 constructor
 · change S⁻¹ *ᵥ a = _
   rw [← hcol1]
   exact go _
 constructor
 · change S⁻¹ *ᵥ b = _
   rw [← hcol2]
   exact go _
 · change S⁻¹ *ᵥ c = _
   rw [← hcol3]
   exact go _
set_option maxRecDepth 100000 in
lemma back_col (a b c w:Fin 3→ℝ) (hn:(cols a b c).det≠0) :
 cols a b c *ᵥ ((cols a b c)⁻¹ *ᵥ w) = w := by
 rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hn),
       Matrix.one_mulVec]
-- quad combo
set_option maxRecDepth 100000 in
lemma quad2 (M:Matrix (Fin 3) (Fin 3) ℝ) (hM:M.IsSymm)
 (a b:Fin 3→ℝ) (s t:ℝ)
 (qa:a ⬝ᵥ(M*ᵥa)=0) (qb:b ⬝ᵥ(M*ᵥb)=0) :
 (s • a + t • b) ⬝ᵥ (M *ᵥ (s • a + t • b)) =
   2*s*t*(a ⬝ᵥ(M*ᵥb)) := by
 rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
     add_dotProduct, dotProduct_add, dotProduct_add,
     smul_dotProduct, smul_dotProduct,
     dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul]
 have eq := bilin_symm M hM b a
 -- inspect
 simp [qa,qb,eq]
 ring
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma triple_nonzero (M:Matrix (Fin 3) (Fin 3) ℝ) (hM:M.IsSymm) (hdet:M.det≠0)
 (a b c:Fin 3→ℝ) (ha:a≠0) (hb:b≠0) (hc:c≠0)
 (hab:¬ SamePoint a b) (hac:¬ SamePoint a c) (hbc:¬ SamePoint b c)
 (qa:a ⬝ᵥ(M*ᵥa)=0) (qb:b ⬝ᵥ(M*ᵥb)=0) (qc:c ⬝ᵥ(M*ᵥc)=0) :
 br[a,b,c] ≠ 0 := by
 have hp : a ⬝ᵥ (M*ᵥb) ≠ 0 := pair_nonzero M hM hdet a b ha hb hab qa qb
 -- setup S0
 let z : Fin 3→ℝ := a ⨯₃ b
 have hz : z ≠ 0 := cross_ne a b ha hb hab
 have hn : (cols a b z).det ≠ 0 := by
   rw [det_cols, triple_product_permutation a b z,
       triple_product_permutation b z a]
   change z ⬝ᵥ z ≠ 0
   exact mt dotProduct_self_eq_zero.mp hz
 let T := (cols a b z)⁻¹
 obtain ⟨Ta,Tb,Tz⟩ := inv_col a b z hn
 -- suppose determinant zero
 intro hd
 have czero : (T *ᵥ c) 2 = 0 := by
   have e := br_mul T a b c
   change br[T*ᵥa,T*ᵥb,T*ᵥc] = T.det * br[a,b,c] at e
   rw [Ta,Tb,hd] at e
   simp [dotProduct, crossProduct, Fin.sum_univ_succ] at e
   exact e
 let s : ℝ := (T *ᵥ c) 0
 let t : ℝ := (T *ᵥ c) 1
 have coord : T *ᵥ c = ![s,t,0] := by
   funext i
   fin_cases i
   · rfl
   · rfl
   · exact czero
 have exp : c = s • a + t • b := by
   have back := back_col a b z c hn
   change cols a b z *ᵥ (T *ᵥ c) = c at back
   rw [coord, cols_mul] at back
   -- back : s•a + t•b + 0•z = c
   simpa using back.symm
 have st : s*t = 0 := by
   rw [exp] at qc -- maybe replaces c in expression and hypotheses hac/hbc? rw at qc safe also M? c variable occurrences
   rw [quad2 M hM a b s t qa qb] at qc
   -- qc : 2*s*t*... =0
   have : 2*s*t*(a ⬝ᵥ(M*ᵥb)) = 0 := qc
   rcases mul_eq_zero.mp this with hst | hpair
   · rcases mul_eq_zero.mp hst with h2s | ht0
     · rcases mul_eq_zero.mp h2s with h2 | hs0
       · norm_num at h2
       · simp [hs0]
     · simp [ht0]
   · exact (hp hpair).elim
 rcases mul_eq_zero.mp st with hs | ht
 · -- s=0 -> c=t b
   have ctb : c = t • b := by rw [exp, hs]; simp
   have tn : t ≠ 0 := by
     intro tt; rw [tt] at ctb; simp at ctb; exact hc ctb
   exact hbc ⟨t, tn, ctb⟩
 · have ca : c = s • a := by rw [exp, ht]; simp
   have sn : s ≠ 0 := by intro ss; rw [ss] at ca; simp at ca; exact hc ca
   exact hac ⟨s,sn,ca⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma gram_quad (M:Matrix (Fin 3) (Fin 3) ℝ) (S:Matrix (Fin 3) (Fin 3) ℝ)
 (x:Fin 3→ℝ):
 x ⬝ᵥ ((Sᵀ * M * S) *ᵥ x) = (S *ᵥ x) ⬝ᵥ (M *ᵥ (S *ᵥ x)) := by
 simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
 ring
-- offdiag entries of Gram in basis a,b,c are A etc via gram_apply
-- normalized target lemma for standard and equation relations
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma normalized (A B C : ℝ) (x y z X Y Z U V W:ℝ)
 (hA : A ≠ 0)
 (q1:A*x*y+B*x*z+C*y*z=0)
 (q2:A*X*Y+B*X*Z+C*Y*Z=0)
 (q3:A*U*V+B*U*W+C*V*W=0) :
 let a : Fin 3 → ℝ := ![1,0,0]
 let b : Fin 3 → ℝ := ![0,1,0]
 let c : Fin 3 → ℝ := ![0,0,1]
 let u : Fin 3 → ℝ := ![x,y,z]
 let v : Fin 3 → ℝ := ![X,Y,Z]
 let w : Fin 3 → ℝ := ![U,V,W]
 (((a ⨯₃ v) ⨯₃ (b ⨯₃ u)) ⬝ᵥ
             (((a ⨯₃ w) ⨯₃ (c ⨯₃ u)) ⨯₃
              ((b ⨯₃ w) ⨯₃ (c ⨯₃ v)))) = 0 := by
 dsimp
 -- use stdid then N
 rw [stdid x y z X Y Z U V W]
 -- cofactor combination
 have zer : A * ( y*z * (X*Z*U*V - X*Y*U*W) -
   x*z * (Y*Z*U*V - X*Y*V*W) +
   x*y * (Y*Z*U*W - X*Z*V*W)) = 0 := by
  linear_combination
    (Y*Z*U*W-X*Z*V*W)*q1 +
    (x*z*V*W-y*z*U*W)*q2 +
    (y*z*X*Z-x*z*Y*Z)*q3
 -- if zer
 rcases mul_eq_zero.mp zer with ha|hf
 · exact (hA ha).elim
 · exact hf
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma coord_quad (M:Matrix (Fin 3) (Fin 3) ℝ) (hM:M.IsSymm)
 (a b c u:Fin 3→ℝ)
 (qa:a⬝ᵥ(M*ᵥa)=0) (qb:b⬝ᵥ(M*ᵥb)=0) (qc:c⬝ᵥ(M*ᵥc)=0) :
 u ⬝ᵥ (((cols a b c)ᵀ * M * (cols a b c)) *ᵥ u) =
 2 * ((a⬝ᵥ(M*ᵥb))*u 0*u 1 + (a⬝ᵥ(M*ᵥc))*u 0*u 2 + (b⬝ᵥ(M*ᵥc))*u 1*u 2) := by
 simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
 -- yields entries apply; rewrite via gram_apply
 simp_rw [gram_apply]
 simp
 -- entries matrix indices (![a,b,c] i) evaluation; simp
 rw [bilin_symm M hM b a, bilin_symm M hM c a, bilin_symm M hM c b]
 rw [qa,qb,qc]
 simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
 ring
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
lemma master (M:Matrix (Fin 3) (Fin 3) ℝ) (hM:M.IsSymm)(hdet:M.det≠0)
 (a b c d e f:Fin 3→ℝ)
 (ha:a≠0)(hb:b≠0)(hc:c≠0)
 (hab:¬ SamePoint a b)(hac:¬ SamePoint a c)(hbc:¬ SamePoint b c)
 (qa:a⬝ᵥ(M*ᵥa)=0)(qb:b⬝ᵥ(M*ᵥb)=0)(qc:c⬝ᵥ(M*ᵥc)=0)
 (qd:d⬝ᵥ(M*ᵥd)=0)(qe:e⬝ᵥ(M*ᵥe)=0)(qf:f⬝ᵥ(M*ᵥf)=0) :
 (((a ⨯₃ e) ⨯₃ (b ⨯₃ d)) ⬝ᵥ
   (((a ⨯₃ f) ⨯₃ (c ⨯₃ d)) ⨯₃ ((b ⨯₃ f) ⨯₃ (c ⨯₃ e)))) = 0 := by
 have hdabc := triple_nonzero M hM hdet a b c ha hb hc hab hac hbc qa qb qc
 have hn : (cols a b c).det ≠ 0 := by rw [det_cols]; exact hdabc
 let T : Matrix (Fin 3) (Fin 3) ℝ := (cols a b c)⁻¹
 obtain ⟨Ta,Tb,Tc⟩ := inv_col a b c hn
 let u : Fin 3→ℝ := T *ᵥ d
 let v : Fin 3→ℝ := T *ᵥ e
 let w : Fin 3→ℝ := T *ᵥ f
 have ueq : u = ![u 0,u 1,u 2] := by funext i; fin_cases i <;> rfl
 have veq : v = ![v 0,v 1,v 2] := by funext i; fin_cases i <;> rfl
 have weq : w = ![w 0,w 1,w 2] := by funext i; fin_cases i <;> rfl
 let A:ℝ := a⬝ᵥ(M*ᵥb)
 let B:ℝ := a⬝ᵥ(M*ᵥc)
 let C:ℝ := b⬝ᵥ(M*ᵥc)
 have An : A ≠ 0 := pair_nonzero M hM hdet a b ha hb hab qa qb
 have uq : A*u 0*u 1+B*u 0*u 2+C*u 1*u 2 = 0 := by
   have back := gram_quad M (cols a b c) u
   have hbck := back_col a b c d hn
   change cols a b c *ᵥ u = d at hbck
   rw [hbck, qd] at back
   -- back : ... = 0
   rw [coord_quad M hM a b c u qa qb qc] at back
   change 2 * (A*u 0*u 1+B*u 0*u 2+C*u 1*u 2) = 0 at back
   linarith
 have vq : A*v 0*v 1+B*v 0*v 2+C*v 1*v 2 = 0 := by
   have back := gram_quad M (cols a b c) v
   have hbck := back_col a b c e hn
   change cols a b c *ᵥ v = e at hbck
   rw [hbck, qe] at back
   rw [coord_quad M hM a b c v qa qb qc] at back
   change 2 * (A*v 0*v 1+B*v 0*v 2+C*v 1*v 2) = 0 at back
   linarith
 have wq : A*w 0*w 1+B*w 0*w 2+C*w 1*w 2 = 0 := by
   have back := gram_quad M (cols a b c) w
   have hbck := back_col a b c f hn
   change cols a b c *ᵥ w = f at hbck
   rw [hbck, qf] at back
   rw [coord_quad M hM a b c w qa qb qc] at back
   change 2 * (A*w 0*w 1+B*w 0*w 2+C*w 1*w 2) = 0 at back
   linarith
 have std := normalized A B C (u 0) (u 1) (u 2) (v 0) (v 1) (v 2)
    (w 0) (w 1) (w 2) An uq vq wq
 -- simplify lets std equation
 dsimp at std
 have trans := F_mul T a b c d e f
 change
  ((((T*ᵥa) ⨯₃ (T*ᵥe)) ⨯₃ ((T*ᵥb) ⨯₃ (T*ᵥd))) ⬝ᵥ
    ((((T*ᵥa) ⨯₃ (T*ᵥf)) ⨯₃ ((T*ᵥc) ⨯₃ (T*ᵥd))) ⨯₃
      (((T*ᵥb) ⨯₃ (T*ᵥf)) ⨯₃ ((T*ᵥc) ⨯₃ (T*ᵥe))))) = _ at trans
 -- relate left via std

 change T*ᵥa = _ at Ta
 change T*ᵥb = _ at Tb
 change T*ᵥc = _ at Tc
 rw [Ta,Tb,Tc] at trans
 -- fold transformed remaining
 change
  ((![ (1:ℝ),0,0] ⨯₃ v) ⨯₃ (![0,1,0] ⨯₃ u)) ⬝ᵥ
    (((![1,0,0] ⨯₃ w) ⨯₃ (![0,0,1] ⨯₃ u)) ⨯₃
      ((![0,1,0] ⨯₃ w) ⨯₃ (![0,0,1] ⨯₃ v))) = _ at trans
 rw [ueq,veq,weq] at trans
 rw [std] at trans
 have tdet : T.det ≠ 0 := by
   change ((cols a b c)⁻¹).det ≠ 0
   rw [Matrix.det_nonsing_inv]
   -- inverse scalar
   simpa [Ring.inverse_eq_inv] using (inv_ne_zero hn)
 rcases mul_eq_zero.mp trans.symm with hpow | hh
 · exact (pow_ne_zero 4 tdet hpow).elim
 · exact hh

end

/-ResultProofDefinitionsEnd-/


theorem pascal (M : Matrix (Fin 3) (Fin 3) ℝ) (hMsymm : M.IsSymm) (hMdet : M.det ≠ 0)
    (a₁ a₂ a₃ b₁ b₂ b₃ : Fin 3 → ℝ)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hb₃ : b₃ ≠ 0)
    (hdist : [a₁, a₂, a₃, b₁, b₂, b₃].Pairwise (fun v w => ¬ SamePoint v w))
    (hA₁ : OnConic M a₁) (hA₂ : OnConic M a₂) (hA₃ : OnConic M a₃)
    (hB₁ : OnConic M b₁) (hB₂ : OnConic M b₂) (hB₃ : OnConic M b₃) :
    Collinear3 (meet a₁ b₂ a₂ b₁) (meet a₁ b₃ a₃ b₁) (meet a₂ b₃ a₃ b₂) := by
  have H := hdist
  simp at H
  have hab : ¬ SamePoint a₁ a₂ := H.1.1
  have hac : ¬ SamePoint a₁ a₃ := H.1.2.1
  have hbc : ¬ SamePoint a₂ a₃ := H.2.1.1
  change (((a₁ ⨯₃ b₂) ⨯₃ (a₂ ⨯₃ b₁)) ⬝ᵥ
    (((a₁ ⨯₃ b₃) ⨯₃ (a₃ ⨯₃ b₁)) ⨯₃
      ((a₂ ⨯₃ b₃) ⨯₃ (a₃ ⨯₃ b₂)))) = 0
  apply master M hMsymm hMdet a₁ a₂ a₃ b₁ b₂ b₃ ha₁ ha₂ ha₃ hab hac hbc
  · exact hA₁
  · exact hA₂
  · exact hA₃
  · exact hB₁
  · exact hB₂
  · exact hB₃


end Submission
