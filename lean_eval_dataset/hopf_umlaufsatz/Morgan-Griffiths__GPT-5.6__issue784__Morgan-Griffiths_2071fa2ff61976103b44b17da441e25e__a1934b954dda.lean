import ChallengeDeps

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Basic.lean
set_option linter.all false
namespace H
open scoped Interval Topology
theorem integral_deriv_contDiff_one {E:Type*}
   [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
   (f:ℝ → E) (hf:ContDiff ℝ 1 f) (a b:ℝ) :
   (∫ t in a..b,deriv f t) = f b - f a:=by
 apply intervalIntegral.integral_deriv_eq_sub
 · intro x hx
   exact (hf.differentiable (by exact one_ne_zero)).differentiableAt
 · exact (hf.continuous_deriv (by norm_num)).intervalIntegrable a b
theorem deriv_shift {E:Type*}
   [NormedAddCommGroup E] [NormedSpace ℝ E]
   (f:ℝ → E) (hf:Differentiable ℝ f) (c x:ℝ) :
   deriv (fun t:ℝ => f (t + c)) x = deriv f (x + c):=by
 have houter:HasDerivAt f (deriv f (x+c)) (x+c) :=
   (hf.differentiableAt (x:=x+c)).hasDerivAt
 have hinner:HasDerivAt (fun t:ℝ => t + c) 1 x:=(hasDerivAt_id x).add_const c
 have hcomp:=houter.scomp x hinner
 simpa [Function.comp_def] using hcomp.deriv
theorem deriv_period_endpoint {E:Type*}
   [NormedAddCommGroup E] [NormedSpace ℝ E]
   (f:ℝ → E) (hf:Differentiable ℝ f) (c:ℝ)
   (hp:Function.Periodic f c) :
   deriv f c = deriv f 0:=by
 have funeq:(fun t:ℝ => f (t + c)) = f:=by
   funext t
   exact hp t
 have deq:=congrArg (fun g:ℝ → E => deriv g 0) funeq
 rw [deriv_shift f hf c 0] at deq
 simpa using deq
theorem angle_eq_mod_two_pi (x y:ℝ)
   (hc:Real.cos x = Real.cos y)
   (hs:Real.sin x = Real.sin y) :
   ∃ n:ℤ,y = (n:ℝ) * (2 * Real.pi) + x:=by
 rcases (Real.cos_eq_cos_iff.mp hc) with ⟨k,hk | hk⟩
 · refine ⟨k,?_⟩
   convert hk using 1 <;> ring
 · have hk':y = (k:ℝ) * (2 * Real.pi) - x:=by
     convert hk using 1 <;> ring
   have hneg:Real.sin y = - Real.sin x:=by
     rw [hk',Real.sin_int_mul_two_pi_sub]
   have hx0:Real.sin x = 0:=by
     linarith
   rcases (Real.sin_eq_zero_iff.mp hx0) with ⟨m,hm⟩
   refine ⟨k - m,?_⟩
   rw [hk']
   rw [← hm]
   push_cast
   ring
end H
namespace H
theorem continuous_integer_constant (g:ℝ → ℝ) (hg:Continuous g)
   (hZ:∀t,∃ k:ℤ,g t = (k:ℝ)) :
   ∀t:ℝ,g t = g 0:=by
 intro t
 obtain ⟨m,hm⟩:=hZ 0
 obtain ⟨n,hn⟩:=hZ t
 by_cases hmn:m = n
 · simpa [hm,hn,hmn]
 have hcases:m < n ∨ n < m:=lt_or_gt_of_ne hmn
 rcases hcases with hlt | hlt
 ·
   have hmn':m + 1 ≤ n:=by omega
   let q:ℝ:=(m:ℝ) + (1/2:ℝ)
   have hqlo:g 0 ≤ q:=by dsimp [q]; rw [hm]; linarith
   have hqhi:q ≤ g t:=by
     dsimp [q]
     rw [hn]
     have hcast:((m+1:ℤ):ℝ) ≤ (n:ℝ):=by exact_mod_cast hmn'
     push_cast at hcast
     linarith
   have hq:q ∈ Set.Icc (g 0) (g t):=⟨hqlo,hqhi⟩
   have hrange:q ∈ Set.range g :=
     intermediate_value_univ (0:ℝ) t hg hq
   rcases hrange with ⟨u,hu⟩
   obtain ⟨k,hk⟩:=hZ u
   have hqk:(k:ℝ) = (m:ℝ) + (1/2:ℝ):=by
     calc
       (k:ℝ) = g u:=hk.symm
       _ = q:=hu
       _ = _:=by rfl
   have hklo:m < k:=by
     have hh:(m:ℝ) < (k:ℝ):=by rw [hqk]; linarith
     exact_mod_cast hh
   have hkhi:k < m + 1:=by
     have hh:(k:ℝ) < (m+1:ℤ):=by
       rw [hqk]
       push_cast
       linarith
     exact_mod_cast hh
   omega
 · have hnm':n + 1 ≤ m:=by omega
   let q:ℝ:=(m:ℝ) - (1/2:ℝ)
   have hqlo:g t ≤ q:=by
     dsimp [q]
     rw [hn]
     have hcast:((n+1:ℤ):ℝ) ≤ (m:ℝ):=by exact_mod_cast hnm'
     push_cast at hcast
     linarith
   have hqhi:q ≤ g 0:=by dsimp [q]; rw [hm]; linarith
   have hq:q ∈ Set.Icc (g t) (g 0):=⟨hqlo,hqhi⟩
   have hrange:q ∈ Set.range g :=
     intermediate_value_univ t (0:ℝ) hg hq
   rcases hrange with ⟨u,hu⟩
   obtain ⟨k,hk⟩:=hZ u
   have hqk:(k:ℝ) = (m:ℝ) - (1/2:ℝ):=by
     calc
       (k:ℝ) = g u:=hk.symm
       _ = q:=hu
       _ = _:=by rfl
   have hklo:m - 1 < k:=by
     have hh:((m-1:ℤ):ℝ) < (k:ℝ):=by
       rw [hqk]
       push_cast
       linarith
     exact_mod_cast hh
   have hkhi:k < m:=by
     have hh:(k:ℝ) < (m:ℝ):=by rw [hqk]; linarith
     exact_mod_cast hh
   omega
theorem deriv_period_add {E:Type*}
   [NormedAddCommGroup E] [NormedSpace ℝ E]
   (f:ℝ → E) (hf:Differentiable ℝ f) (c:ℝ)
   (hp:Function.Periodic f c) (x:ℝ) :
   deriv f (x+c) = deriv f x:=by
 have funeq:(fun t:ℝ => f (t + c)) = f:=by
   funext t
   exact hp t
 have deq:=congrArg (fun g:ℝ → E => deriv g x) funeq
 rw [deriv_shift f hf c x] at deq
 exact deq
end H
namespace H
theorem angle_increment_constant (a:ℝ → ℝ) (ha:Continuous a) (c:ℝ)
   (hc:∀t:ℝ,Real.cos (a t) = Real.cos (a (t+c)))
   (hs:∀t:ℝ,Real.sin (a t) = Real.sin (a (t+c))) :
   ∀t:ℝ,a (t+c) - a t = a (0+c) - a 0:=by
 let T:ℝ:=2 * Real.pi
 have hT:T ≠ 0:=by
   dsimp [T]
   have hp:=Real.pi_pos
   positivity
 let g:ℝ → ℝ:=fun t => (a (t+c) - a t) / T
 have hcontshift:Continuous (fun t:ℝ => a (t+c)):=by
   exact ha.comp (continuous_id.add continuous_const)
 have hcont:Continuous g:=by
   dsimp [g]
   fun_prop
 have hZ:∀t,∃ k:ℤ,g t = (k:ℝ):=by
   intro t
   rcases angle_eq_mod_two_pi (a t) (a (t+c)) (hc t) (hs t) with ⟨k,hk⟩
   refine ⟨k,?_⟩
   dsimp [g,T]
   rw [hk]
   have hpi:(2:ℝ) * Real.pi ≠ 0:=by positivity
   field_simp
   <;> ring
 have hgc:=continuous_integer_constant g hcont hZ
 intro t
 have heq:=hgc t
 dsimp [g] at heq
 apply (div_left_inj' hT).mp
 simpa using heq
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Basic.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/LineArea.lean
set_option linter.all false

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/LineArea.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Quad.lean
set_option linter.all false

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Quad.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Shear.lean
set_option linter.all false
namespace H
open scoped BigOperators
lemma exists_Ioo_not_mem_finset (B:Finset ℝ) {a b:ℝ} (hab:a < b) :
   ∃q:ℝ,q ∈ Set.Ioo a b ∧ q ∉ B:=by
 classical
 by_contra! h
 have hsub:Set.Ioo a b ⊆ (↑B:Set ℝ):=by
   intro q hq
   exact_mod_cast (h q hq)
 have hfin:(Set.Ioo a b).Finite:=(B.finite_toSet.subset hsub)
 exact (Set.Ioo_infinite hab) hfin
lemma exists_small_shear
   (X Y:ℕ → ℝ) (S:Finset ℕ)
   (sep:∀i ∈ S,∀j ∈ S,i ≠ j → X i ≠ X j ∨ Y i ≠ Y j)
   {c:ℝ} (hc:0 < c) :
   ∃q:ℝ,|q| < c ∧
     ∀i ∈ S,∀j ∈ S,i ≠ j → Y i + q * X i ≠ Y j + q * X j:=by
 classical
 let bad:ℝ → Prop:=fun q => ∃i ∈ S,∃j ∈ S,
     X i ≠ X j ∧ q = (Y j - Y i) / (X i - X j)
 let B:Finset ℝ:=S.biUnion (fun i =>
   S.biUnion (fun j => if X i = X j then ∅
      else {(Y j - Y i)/(X i - X j)}))
 obtain ⟨q,hq,hqB⟩ :=
   exists_Ioo_not_mem_finset B (show -c < c by linarith)
 have hnotbad:¬ bad q:=by
   intro hb
   rcases hb with ⟨i,hi,j,hj,hijx,he⟩
   have hm:(Y j - Y i)/(X i - X j) ∈
       (if X i = X j then (∅:Finset ℝ)
        else {(Y j - Y i)/(X i - X j)}):=by
     simp [hijx]
   have hmj:(Y j - Y i)/(X i - X j) ∈
       S.biUnion (fun j => if X i = X j then ∅
         else {(Y j - Y i)/(X i - X j)}):=by
     exact Finset.mem_biUnion.mpr ⟨j,hj,hm⟩
   have hmall:(Y j - Y i)/(X i - X j) ∈ B:=by
     exact Finset.mem_biUnion.mpr ⟨i,hi,hmj⟩
   have:q ∈ B:=by simpa [he] using hmall
   exact hqB this
 refine ⟨q,(abs_lt.mpr hq),?_⟩
 intro i hi j hj hij
 intro heq
 by_cases hx:X i = X j
 · have hy:Y i = Y j:=by
     rw [hx] at heq
     linarith
   rcases (sep i hi j hj hij) with h | h <;> contradiction
 · have hxsub:X i - X j ≠ 0:=sub_ne_zero.mpr hx
   apply hnotbad
   refine ⟨i,hi,j,hj,hx,?_⟩
   apply (eq_div_iff hxsub).2
   nlinarith [heq]
lemma det_shear (x y u v q:ℝ) :
   x * (v + q*u) - (y + q*x) * u = x*v - y*u:=by ring
lemma shear_affine_eq_iff (x₀ x₁ y₀ y₁ u₀ u₁ v₀ v₁ q l m:ℝ) :
  ((1-l)*x₀ + l*x₁ = (1-m)*u₀ + m*u₁ ∧
   (1-l)*(y₀+q*x₀) + l*(y₁+q*x₁) =
     (1-m)*(v₀+q*u₀) + m*(v₁+q*u₁)) ↔
  ((1-l)*x₀ + l*x₁ = (1-m)*u₀ + m*u₁ ∧
   (1-l)*y₀ + l*y₁ = (1-m)*v₀ + m*v₁):=by
 constructor
 · rintro ⟨hx,hq⟩
   constructor
   · exact hx
   · calc
       (1-l)*y₀ + l*y₁ =
           ((1-l)*(y₀+q*x₀) + l*(y₁+q*x₁)) -
              q * ((1-l)*x₀ + l*x₁):=by ring
       _ = ((1-m)*(v₀+q*u₀) + m*(v₁+q*u₁)) -
              q * ((1-m)*u₀ + m*u₁):=by rw [hq,hx]
       _ = (1-m)*v₀ + m*v₁:=by ring
 · rintro ⟨hx,hy⟩
   constructor
   · exact hx
   · calc
       (1-l)*(y₀+q*x₀) + l*(y₁+q*x₁) =
           ((1-l)*y₀ + l*y₁) + q*((1-l)*x₀ + l*x₁):=by ring
       _ = ((1-m)*v₀ + m*v₁) + q*((1-m)*u₀ + m*u₁):=by rw [hy,hx]
       _ = (1-m)*(v₀+q*u₀) + m*(v₁+q*u₁):=by ring
lemma shear_end_signs {b e A D q:ℝ}
   (hb:0 < b) (he:e < 0)
   (hq₁:|q| < b / (|A|+1))
   (hq₂:|q| < (-e) / (|D|+1)) :
   0 < b + q*A ∧ e + q*D < 0:=by
 have hA:0 < |A|+1:=by
   have:=abs_nonneg A
   linarith
 have hD:0 < |D|+1:=by
   have:=abs_nonneg D
   linarith
 have hqa:|q| * |A| < b:=by
   have ht:=(lt_div_iff₀ hA).1 hq₁
   calc
     |q| * |A| ≤ |q| * (|A|+1):=by
       have hq0:0 ≤ |q|:=abs_nonneg _
       nlinarith
     _ < b:=by simpa [mul_add] using ht
 have hqd:|q| * |D| < -e:=by
   have ht:=(lt_div_iff₀ hD).1 hq₂
   calc
     |q| * |D| ≤ |q| * (|D|+1):=by
       have hq0:0 ≤ |q|:=abs_nonneg _
       nlinarith
     _ < -e:=by simpa [mul_add] using ht
 have ha:|q*A| < b:=by simpa [abs_mul,mul_comm] using hqa
 have hd:|q*D| < -e:=by simpa [abs_mul,mul_comm] using hqd
 constructor
 · have hlo:=(abs_lt.mp ha).1
   linarith
 · have hhi:=(abs_lt.mp hd).2
   linarith
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Shear.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Chords.lean
set_option linter.all false
namespace H
open scoped Interval Topology
section
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
noncomputable def MV (f:ℝ → E) (s h:ℝ):E :=
 ∫ u in (0:ℝ)..1,deriv f (h*u+s)
lemma continuous_meanVelocity (f:ℝ → E) (hf:ContDiff ℝ 1 f) :
   Continuous (fun q:ℝ × ℝ => MV f q.1 q.2):=by
 have hv:Continuous (deriv f):=hf.continuous_deriv (by norm_num)
 let F:(ℝ × ℝ) → ℝ → E:=fun q u => deriv f (q.2*u+q.1)
 have hF:Continuous F.uncurry:=by
   dsimp [F,Function.uncurry]
   fun_prop
 have hI:Continuous (fun q:ℝ × ℝ => ∫ u in (0:ℝ)..1,F q u) :=
   intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
     (μ:=MeasureTheory.MeasureSpace.volume) hF 0 1
 simpa [MV,F] using hI
lemma continuous_meanVelocity_comp {X:Type*} [TopologicalSpace X]
   (f:ℝ → E) (hf:ContDiff ℝ 1 f) (s h:X → ℝ)
   (hs:Continuous s) (hh:Continuous h) :
   Continuous (fun x => MV f (s x) (h x)):=by
 exact (continuous_meanVelocity f hf).comp (hs.prodMk hh)
@[simp] lemma meanVelocity_zero (f:ℝ → E) (hf:Differentiable ℝ f)
   (s:ℝ):MV f s 0 = deriv f s:=by
 unfold MV
 simp
lemma smul_meanVelocity (f:ℝ → E) (hf:ContDiff ℝ 1 f)
   (s h:ℝ):h • MV f s h = f (s+h) - f s:=by
 unfold MV
 calc
   h • (∫ u in (0:ℝ)..1,deriv f (h*u+s)) =
       ∫ v in h * (0:ℝ) + s..h * 1 + s,deriv f v:=by
         simpa using (intervalIntegral.smul_integral_comp_mul_add
           (f:=fun v:ℝ => deriv f v) (a:=(0:ℝ)) (b:=1) h s)
   _ = f (s+h) - f s:=by
     simpa [add_comm,add_left_comm,add_assoc] using
       (integral_deriv_contDiff_one f hf s (s+h))
lemma neg_smul_meanVelocity_sub_period (f:ℝ → E) (hf:ContDiff ℝ 1 f)
   {p:ℝ} (hp:Function.Periodic f p) (s h:ℝ) :
   -(p-h) • MV f s (h-p) = f (s+h) - f s:=by
 have hper:f (s + h) = f (s + (h-p)):=by
   have heq:(s + (h-p)) + p = s + h:=by ring
   rw [← heq,hp]
 rw [hper]
 have hc:-(p-h) = h-p:=by ring
 rw [hc]
 exact smul_meanVelocity f hf s (h-p)
lemma meanVelocity_ne_zero_of_ne (f:ℝ → E) (hf:ContDiff ℝ 1 f)
   {s h:ℝ} (hends:f (s+h) ≠ f s):MV f s h ≠ 0:=by
 intro hz
 have hd:=smul_meanVelocity f hf s h
 rw [hz,smul_zero] at hd
 exact hends (sub_eq_zero.mp hd.symm)
lemma meanVelocity_reverse_from_zero (f:ℝ → E) (hf:ContDiff ℝ 1 f)
   (s:ℝ):MV f s (-s) = MV f 0 s:=by
 by_cases hs:s = 0
 · subst s; simp [meanVelocity_zero,hf.differentiable (by exact one_ne_zero)]
 · apply (smul_right_injective E hs)
   have h1:=smul_meanVelocity f hf 0 s
   have h2:=smul_meanVelocity f hf s (-s)
   have h2':s • MV f s (-s) = f s - f 0:=by
     have h:=congrArg Neg.neg h2
     simpa [neg_smul] using h
   have h1':s • MV f 0 s = f s - f 0:=by simpa using h1
   exact h2'.trans h1'.symm
lemma deriv_periodic (f:ℝ → E) (hf:Differentiable ℝ f) {p x:ℝ}
   (hp:Function.Periodic f p):deriv f (x+p) = deriv f x :=
 deriv_period_add f hf p hp x
lemma meanVelocity_across_period (f:ℝ → E) (hf:ContDiff ℝ 1 f)
   {p:ℝ} (hp:Function.Periodic f p) (s:ℝ) :
   MV f s (p-s) = MV f 0 (s-p):=by
 by_cases hs:p - s = 0
 · have hsp:s = p:=sub_eq_zero.mp hs |>.symm
   subst s
   have hd:=deriv_periodic f (hf.differentiable (by exact one_ne_zero)) (x:=0) hp
   simpa [meanVelocity_zero,hf.differentiable (by exact one_ne_zero)] using hd
 · apply (smul_right_injective E hs)
   have h1:=smul_meanVelocity f hf s (p-s)
   have h2:=smul_meanVelocity f hf 0 (s-p)
   have hper0:f p = f 0:=by simpa using hp 0
   have hmove:f (s-p) = f s:=by
     have hh:=hp (s-p)
     have heq:(s-p) + p = s:=by ring
     rw [heq] at hh
     exact hh.symm
   have h2':(p-s) • MV f 0 (s-p) = f 0 - f s:=by
     have hh:=congrArg Neg.neg h2
     have hend:f (0 + (s-p)) = f s:=by simpa using hmove
     rw [hend] at hh
     have hcoef:-(s-p) = p-s:=by ring
     calc
       (p-s) • MV f 0 (s-p) =
           -((s-p) • MV f 0 (s-p)):=by rw [← neg_smul,hcoef]
       _ = f 0 - f s:=by simpa [sub_eq_add_neg,add_comm] using hh
   have h1':(p-s) • MV f s (p-s) = f 0 - f s:=by
     have hend:f (s + (p-s)) = f 0:=by
       have e:s + (p-s) = p:=by ring
       rw [e,hper0]
     rw [hend] at h1
     exact h1
   exact h1'.trans h2'.symm
end
lemma triangle_endpoints_ne {E:Type*} (f:ℝ → E) {p s t:ℝ}
   (hp0:0 < p) (hper:Function.Periodic f p)
   (hinj:Set.InjOn f (Set.Ico (0:ℝ) p))
   (hs:0 ≤ s) (hst:s ≤ t) (ht:t ≤ p)
   (hne:s < t) (hvtx:s ≠ 0 ∨ t ≠ p) :
   f t ≠ f s:=by
 intro he
 by_cases ht':t < p
 · have hs':s < p:=lt_of_le_of_lt hst ht'
   have hmS:s ∈ Set.Ico (0:ℝ) p:=⟨hs,hs'⟩
   have ht0:0 ≤ t:=le_trans hs hst
   have hmT:t ∈ Set.Ico (0:ℝ) p:=⟨ht0,ht'⟩
   have eqst:t = s:=hinj hmT hmS he
   exact (ne_of_gt hne) eqst
 · have htEq:t = p:=le_antisymm ht (le_of_not_gt ht')
   subst t
   have he0:f 0 = f s:=by
     calc
       f 0 = f p:=(by simpa using (hper 0).symm)
       _ = f s:=he
   by_cases hs0:s = 0
   · exact (False.elim ((hvtx.elim (fun h => h hs0) (fun h => h rfl))))
   · have hslt:s < p:=by simpa using hne
     have hmS:s ∈ Set.Ico (0:ℝ) p:=⟨hs,hslt⟩
     have hm0:(0:ℝ) ∈ Set.Ico (0:ℝ) p:=⟨le_rfl,hp0⟩
     have eq0s:(0:ℝ) = s:=hinj hm0 hmS he0
     exact hs0 eq0s.symm
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Chords.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Sweep.lean
set_option linter.all false
namespace H
open scoped BigOperators
def SA (Y:ℕ → ℝ) (i:ℕ) (z:ℝ):Prop :=
 (Y i < z ∧ z < Y (i+1)) ∨ (Y (i+1) < z ∧ z < Y i)
noncomputable def SP (Y:ℕ → ℝ) (i:ℕ) (z:ℝ):ℝ :=
 (z - Y i) / (Y (i+1) - Y i)
noncomputable def SX (X Y:ℕ → ℝ) (i:ℕ) (z:ℝ):ℝ :=
 (1 - SP Y i z) * X i + (SP Y i z) * X (i+1)
lemma active_ne {Y:ℕ → ℝ} {i:ℕ} {z:ℝ}
   (h:SA Y i z):Y (i+1) - Y i ≠ 0:=by
 rcases h with h | h
 · have:Y i < Y (i+1):=lt_trans h.1 h.2
   linarith
 · have:Y (i+1) < Y i:=lt_trans h.1 h.2
   linarith
lemma param_pos_lt_one {Y:ℕ → ℝ} {i:ℕ} {z:ℝ}
   (h:SA Y i z) :
   0 < SP Y i z ∧ SP Y i z < 1:=by
 rcases h with h | h
 · dsimp [SP]
   have hd:0 < Y (i+1) - Y i:=by linarith
   constructor
   · exact div_pos (by linarith) hd
   · apply (div_lt_iff₀ hd).2
     linarith
 · dsimp [SP]
   have hd:Y (i+1) - Y i < 0:=by linarith
   constructor
   · exact div_pos_of_neg_of_neg (by linarith) hd
   · apply (div_lt_iff_of_neg hd).2
     linarith
lemma slice_height {Y:ℕ → ℝ} {i:ℕ} {z:ℝ}
   (h:SA Y i z) :
   (1 - SP Y i z) * Y i + SP Y i z * Y (i+1) = z:=by
 have hd:=active_ne h
 dsimp [SP]
 field_simp
 ring_nf
lemma slice_ne_of_halfopen
   (X Y:ℕ → ℝ) {n:ℕ}
   (edge:∀i j:ℕ,i < j → j < n → ∀l m:ℝ,0 ≤ l → l < 1 → 0 ≤ m → m < 1 → ((1-l)*X i + l*X (i+1) ≠ (1-m)*X j + m*X (j+1)) ∨
         ((1-l)*Y i + l*Y (i+1) ≠ (1-m)*Y j + m*Y (j+1)))
   {i j:ℕ} (hij:i < j) (hj:j < n) {z:ℝ}
   (hi:SA Y i z) (hja:SA Y j z) :
   SX X Y i z ≠ SX X Y j z:=by
 intro he
 have hpi:=param_pos_lt_one hi
 have hpj:=param_pos_lt_one hja
 have hyi:=slice_height hi
 have hyj:=slice_height hja
 have hbad:=edge i j hij hj (SP Y i z) (SP Y j z)
         hpi.1.le hpi.2 hpj.1.le hpj.2
 rcases hbad with hbad | hbad
 · exact hbad he
 · exact hbad (hyi.trans hyj.symm)
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Sweep.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Triangle.lean
set_option linter.all false
namespace H
def CT (p:ℝ):Set (ℝ × ℝ):={q | 0 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ p}
lemma convex_chordTriangle (p:ℝ):Convex ℝ (CT p):=by
 intro x hx y hy a b ha hb hab
 rcases hx with ⟨hx0,hxy,hxp⟩
 rcases hy with ⟨hy0,hyy,hyp⟩
 change 0 ≤ _ ∧ _ ≤ _ ∧ _ ≤ _
 dsimp
 constructor
 · positivity
 constructor
 · nlinarith
 · nlinarith
lemma nonempty_chordTriangle {p:ℝ} (hp:0 ≤ p):(CT p).Nonempty :=
 ⟨(0,0),by exact ⟨le_rfl,le_rfl,hp⟩⟩
noncomputable instance instLocPathChordTriangle (p:ℝ) :
   LocPathConnectedSpace (CT p) :=
 (convex_chordTriangle p).locPathConnectedSpace
noncomputable instance instSimplyConnectedChordTriangle (p:ℝ) [hp: Fact (0 ≤ p)] :
   SimplyConnectedSpace (CT p) :=
 let _:=(convex_chordTriangle p).contractibleSpace (nonempty_chordTriangle hp.1)
 inferInstance
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Triangle.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Lift.lean
set_option linter.all false
namespace H
open scoped Interval Topology
section switch
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [CompleteSpace E]
noncomputable def SC (f:ℝ → E) (p:ℝ) (q:ℝ × ℝ):E :=
 if q.2 - q.1 ≤ p / 2 then
   MV f q.1 (q.2 - q.1)
 else
   - MV f q.1 ((q.2 - q.1) - p)
lemma switchedChord_seam (f:ℝ → E) (hf:ContDiff ℝ 1 f)
   {p:ℝ} (hp0:0 < p) (hper:Function.Periodic f p)
   (q:ℝ × ℝ) (hq:q.2 - q.1 = p / 2) :
   MV f q.1 (q.2-q.1) =
     - MV f q.1 ((q.2-q.1)-p):=by
 have h:=neg_smul_meanVelocity_sub_period f hf hper q.1 (q.2-q.1)
 rw [hq] at h
 have hc:(p / 2:ℝ) ≠ 0:=by positivity
 apply (smul_right_injective E hc)
 have h2:=smul_meanVelocity f hf q.1 (p/2)
 have heq:q.1 + (p/2) = q.1 + (p/2):=rfl
 have hnegcoef:-(p - p/2) = -(p/2):=by ring
 rw [hnegcoef] at h
 have hright :
       (p/2) • (- MV f q.1 (p/2-p))
         = f (q.1 + p/2) - f q.1:=by
   simpa [neg_smul] using h
 simpa [hq] using h2.trans hright.symm
lemma continuous_switchedChord (f:ℝ → E) (hf:ContDiff ℝ 1 f)
   {p:ℝ} (hp0:0 < p) (hper:Function.Periodic f p) :
   Continuous (SC f p):=by
 let u:(ℝ × ℝ) → ℝ:=fun q => q.2 - q.1
 have hu:Continuous u:=by
   dsimp [u]; fun_prop
 have hc:Continuous (fun _q:ℝ × ℝ => p/2):=continuous_const
 have hfirst:Continuous (fun q:ℝ × ℝ => MV f q.1 (q.2-q.1)) :=
   continuous_meanVelocity_comp f hf _ _ continuous_fst
     (by fun_prop)
 have hsecond:Continuous
     (fun q:ℝ × ℝ => - MV f q.1 ((q.2-q.1)-p)) :=
   (continuous_meanVelocity_comp f hf _ _ continuous_fst
     (by fun_prop)).neg
 have h:=hfirst.if_le hsecond hu hc (by
   intro q hq
   dsimp [u] at hq
   exact switchedChord_seam f hf hp0 hper q hq)
 change Continuous (fun q:ℝ × ℝ =>
   if q.2 - q.1 ≤ p/2 then MV f q.1 (q.2-q.1)
   else - MV f q.1 ((q.2-q.1)-p))
 exact h
lemma switchedChord_ne_zero (f:ℝ → E) (hf:ContDiff ℝ 1 f)
   {p:ℝ} (hp0:0 < p) (hper:Function.Periodic f p)
   (hinj:Set.InjOn f (Set.Ico (0:ℝ) p))
   (hv:∀x:ℝ,deriv f x ≠ 0)
   (q:CT p):SC f p q.1 ≠ 0:=by
 classical
 rcases q.2 with ⟨hs,hst,ht⟩
 let h:ℝ:=q.1.2 - q.1.1
 have hh0:0 ≤ h:=by dsimp [h]; linarith
 have hhp:h ≤ p:=by dsimp [h]; linarith
 by_cases hsmall:h ≤ p/2
 · rw [SC]
   split_ifs with hh
   ·
     by_cases heq:h = 0
     · have hstEq:q.1.2 = q.1.1:=by dsimp [h] at heq; linarith
       have hzero:q.1.2 - q.1.1 = 0:=by dsimp [h] at heq; exact heq
       simpa [hzero,meanVelocity_zero,hf.differentiable (by exact one_ne_zero)]
         using (hv q.1.1)
     · have hpos:0 < h:=lt_of_le_of_ne hh0 (Ne.symm heq)
       have hlt:h < p:=lt_of_le_of_lt hsmall (by linarith [hp0])
       have hvtx:q.1.1 ≠ 0 ∨ q.1.2 ≠ p:=by
         classical
         by_contra hnot
         push Not at hnot
         dsimp [h] at hlt
         rw [hnot.1,hnot.2] at hlt
         linarith
       have hend:f q.1.2 ≠ f q.1.1 :=
         triangle_endpoints_ne f hp0 hper hinj hs hst ht
           (by dsimp [h] at hpos; linarith) hvtx
       apply meanVelocity_ne_zero_of_ne f hf
         (s:=q.1.1) (h:=q.1.2-q.1.1)
       simpa using hend
   · exact False.elim (hh (by simpa [h] using hsmall))
 · have hlarge:p/2 < h:=lt_of_not_ge hsmall
   rw [SC]
   split_ifs with hh
   · exact False.elim (hsmall (by simpa [h] using hh))
   ·
     intro hz
     have hz':MV f q.1.1 ((q.1.2-q.1.1)-p) = 0 :=
       neg_eq_zero.mp hz
     by_cases heq:h = p
     ·
       have hs0:q.1.1 = 0:=by dsimp [h] at heq; linarith
       have ht':q.1.2 = p:=by dsimp [h] at heq; linarith
       have harg:(q.1.2-q.1.1)-p = 0:=by rw [hs0,ht']; ring
       have:MV f q.1.1 ((q.1.2-q.1.1)-p)
           = deriv f q.1.1:=by
             simp [harg,meanVelocity_zero,hf.differentiable (by exact one_ne_zero)]
       have hdz:=hv q.1.1
       exact hdz (by simpa [this] using hz')
     · have hlt:h < p:=lt_of_le_of_ne hhp heq
       have hpos:0 < h:=lt_trans (by linarith [hp0]) hlarge
       have hvtx:q.1.1 ≠ 0 ∨ q.1.2 ≠ p:=by
         classical
         by_contra hnot
         push Not at hnot
         dsimp [h] at hlt
         rw [hnot.1,hnot.2] at hlt
         linarith
       have hend:f q.1.2 ≠ f q.1.1 :=
         triangle_endpoints_ne f hp0 hper hinj hs hst ht
           (by dsimp [h] at hpos; linarith) hvtx
       have hm:MV f q.1.1 (q.1.2-q.1.1) ≠ 0 :=
         meanVelocity_ne_zero_of_ne f hf (by simpa using hend)
       have hrel:=neg_smul_meanVelocity_sub_period f hf hper
           q.1.1 (q.1.2-q.1.1)
       rw [hz',smul_zero] at hrel
       have hzeroeq:f (q.1.1 + (q.1.2-q.1.1)) = f q.1.1 :=
         sub_eq_zero.mp hrel.symm
       exact hend (by simpa using hzeroeq)
end switch
def PC (v:EuclideanSpace ℝ (Fin 2)):ℂ:=⟨v 0,v 1⟩
lemma continuous_planeComplex:Continuous PC:=by
 have hh:Continuous (fun v:EuclideanSpace ℝ (Fin 2) =>
     (v 0:ℂ) + (v 1:ℂ) * Complex.I):=by fun_prop
 have heq:PC = (fun v:EuclideanSpace ℝ (Fin 2) =>
     (v 0:ℂ) + (v 1:ℂ) * Complex.I):=by
   funext v
   apply Complex.ext <;> simp [PC]
 rw [heq]
 exact hh
lemma planeComplex_eq_zero_iff (v:EuclideanSpace ℝ (Fin 2)) :
   PC v = 0 ↔ v = 0:=by
 constructor
 · intro h
   have h0:v 0 = 0:=by
     have:=congrArg Complex.re h
     simpa [PC] using this
   have h1:v 1 = 0:=by
     have:=congrArg Complex.im h
     simpa [PC] using this
   ext i
   fin_cases i
   · exact h0
   · exact h1
 · rintro rfl
   rfl
lemma planeComplex_cos_sin (x:ℝ) :
   PC !₂[Real.cos x,Real.sin x] =
     Complex.exp ((x:ℂ) * Complex.I):=by
 rw [Complex.exp_mul_I]
 apply Complex.ext
 · simp [PC,Complex.cos_ofReal_re,Complex.sin_ofReal_re]
 · simp [PC,Complex.cos_ofReal_re,Complex.sin_ofReal_re]
noncomputable def TC (z:ℂ) (hz:z ≠ 0):Circle :=
 ⟨ z / (‖z‖:ℂ),mem_sphere_zero_iff_norm.2 <| by
     rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg z)]
     exact div_self (by simpa using (norm_pos_iff.2 hz).ne') ⟩
@[simp] lemma coe_toCircle (z:ℂ) (hz:z ≠ 0) :
   (TC z hz:ℂ) = z / (‖z‖:ℂ):=rfl
lemma continuous_toCircle {X:Type*} [TopologicalSpace X]
   (z:X → ℂ) (hz:∀x,z x ≠ 0) (hc:Continuous z) :
   Continuous (fun x => TC (z x) (hz x)):=by
 apply Continuous.subtype_mk
 ·
   exact hc.div
     (Complex.continuous_ofReal.comp (continuous_norm.comp hc))
     (fun x => Complex.ofReal_ne_zero.mpr
       ((norm_pos_iff.2 (hz x)).ne'))
section circle
variable (f:ℝ → EuclideanSpace ℝ (Fin 2)) (p:ℝ)
variable (hf:ContDiff ℝ 1 f) (hp0:0 < p)
variable (hper:Function.Periodic f p)
variable (hinj:Set.InjOn f (Set.Ico (0:ℝ) p))
variable (hv:∀x:ℝ,deriv f x ≠ 0)
noncomputable def chordCircle (q:CT p):Circle :=
 TC (PC (SC f p q.1))
   ((planeComplex_eq_zero_iff _).not.mpr
     (switchedChord_ne_zero f hf hp0 hper hinj hv q))
lemma continuous_chordCircle :
   Continuous (chordCircle f p hf hp0 hper hinj hv):=by
 apply continuous_toCircle _ _
 exact continuous_planeComplex.comp
   ((continuous_switchedChord f hf hp0 hper).comp continuous_subtype_val)
theorem exists_chord_lift (a0:ℝ)
   (hbase:deriv f 0 = !₂[Real.cos a0,Real.sin a0]) :
   ∃b:C(CT p,ℝ),
     b ⟨(0,0),by exact ⟨le_rfl,le_rfl,le_of_lt hp0⟩⟩ = a0 ∧
     ∀q:CT p,
       Circle.exp (b q) = chordCircle f p hf hp0 hper hinj hv q:=by
 classical
 letI:Fact (0 ≤ p):=⟨le_of_lt hp0⟩
 let q0:CT p :=
   ⟨(0,0),by exact ⟨le_rfl,le_rfl,le_of_lt hp0⟩⟩
 have he:(Circle.exp a0:Circle) =
     chordCircle f p hf hp0 hper hinj hv q0:=by
   have hv0:SC f p (0,0) = deriv f 0:=by
     have hh:(0:ℝ) ≤ p/2:=by linarith
     simp [SC,hh,meanVelocity_zero,
       hf.differentiable (by exact one_ne_zero)]
   apply Circle.ext
   change ((Circle.exp a0:Circle):ℂ) =
     PC (SC f p (0,0)) /
       (‖PC (SC f p (0,0))‖:ℂ)
   rw [hv0,hbase,planeComplex_cos_sin,Circle.coe_exp,
       Complex.norm_exp]
   simp
 let F:C(CT p,Circle) :=
   ⟨chordCircle f p hf hp0 hper hinj hv,continuous_chordCircle f p hf hp0 hper hinj hv⟩
 obtain ⟨B,hB,_⟩ :=
   Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts F q0 a0 he
 refine ⟨B,hB.1,?_⟩
 intro q
 have hc:=congrArg (fun g => g q) hB.2
 exact hc
end circle
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Lift.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Boundary.lean
set_option linter.all false
namespace H
open scoped Topology
variable (f:ℝ → EuclideanSpace ℝ (Fin 2)) (p:ℝ)
variable (hf:ContDiff ℝ 1 f) (hp0:0 < p)
variable (hper:Function.Periodic f p)
variable (hinj:Set.InjOn f (Set.Ico (0:ℝ) p))
variable (hv:∀x:ℝ,deriv f x ≠ 0)
lemma chordCircle_diagonal (a:ℝ → ℝ)
   (ha:∀x,deriv f x = !₂[Real.cos (a x),Real.sin (a x)])
   {x:ℝ} (hx0:0 ≤ x) (hxp:x ≤ p) :
   chordCircle f p hf hp0 hper hinj hv
     ⟨(x,x),by exact ⟨hx0,le_rfl,hxp⟩⟩ = Circle.exp (a x):=by
 apply Circle.ext
 change PC (SC f p (x,x)) /
      (‖PC (SC f p (x,x))‖:ℂ) = _
 have hh:(0:ℝ) ≤ p/2:=by linarith
 have hvx:SC f p (x,x) = deriv f x:=by
   simp [SC,hh,meanVelocity_zero,
     hf.differentiable (by exact one_ne_zero)]
 rw [hvx,ha,planeComplex_cos_sin,Circle.coe_exp,Complex.norm_exp]
 simp
include hf hper hp0 in
lemma switchedChord_sides {x:ℝ} (hx0:0 ≤ x) (hxp:x ≤ p) :
   SC f p (x,p) = - SC f p (0,x):=by
 by_cases heq:x = p/2
 · subst x
   have hcomp:p - p/2 = p/2:=by ring
   have hc:(p/2:ℝ) ≠ 0:=by positivity
   have hneg:MV f 0 (-(p/2)) =
         - MV f 0 (p/2):=by
       apply (smul_right_injective (EuclideanSpace ℝ (Fin 2)) hc)
       have hpos:=smul_meanVelocity f hf 0 (p/2)
       have hcmp:=neg_smul_meanVelocity_sub_period f hf hper 0 (p/2)
       rw [hcomp] at hcmp
       have harg:p/2-p = -(p/2):=by ring
       rw [harg] at hcmp
       have hcmp':(p/2) • MV f 0 (-(p/2)) =
           -(f (0 + p/2) - f 0):=by
         have hh:=congrArg Neg.neg hcmp
         simpa [neg_smul] using hh
       have hminus :
           (p/2) • (- MV f 0 (p/2)) =
             -(f (0+p/2) - f 0):=by
         simpa [smul_neg] using congrArg Neg.neg hpos
       exact hcmp'.trans hminus.symm
   have across:=meanVelocity_across_period f hf hper (p/2)
   rw [hcomp] at across
   have hfinal:MV f (p/2) (p/2) =
         - MV f 0 (p/2):=by
     calc
       MV f (p/2) (p/2) = MV f 0 (p/2-p):=across
       _ = MV f 0 (-(p/2)):=by congr 2 <;> ring
       _ = _:=hneg
   have hhalf:p/2 ≤ p/2:=le_rfl
   simp [SC,hcomp,hhalf]
   exact hfinal
 · by_cases hx:x ≤ p/2
   · have hlt:x < p/2:=lt_of_le_of_ne hx heq
     have htop:¬ p-x ≤ p/2:=by linarith
     have rev:=meanVelocity_reverse_from_zero f hf x
     change (if p-x ≤ p/2 then _ else _) =
       -(if x-0 ≤ p/2 then _ else _)
     rw [if_neg htop,if_pos (by simpa using hx)]
     have:(p-x)-x-p = -(x+x):=by ring
     simpa using congrArg Neg.neg rev
   · have htop:p-x ≤ p/2:=by linarith
     have across:=meanVelocity_across_period f hf hper x
     change (if p-x ≤ p/2 then _ else _) =
       -(if x-0 ≤ p/2 then _ else _)
     rw [if_pos htop,if_neg (by simpa using hx)]
     simpa using across
lemma chordCircle_sides {x:ℝ} (hx0:0 ≤ x) (hxp:x ≤ p) :
   chordCircle f p hf hp0 hper hinj hv
     ⟨(x,p),by exact ⟨hx0,hxp,le_rfl⟩⟩ =
     - chordCircle f p hf hp0 hper hinj hv
       ⟨(0,x),by exact ⟨le_rfl,hx0,hxp⟩⟩:=by
 apply Circle.ext
 change PC (SC f p (x,p)) /
     (‖PC (SC f p (x,p))‖:ℂ) =
   - (PC (SC f p (0,x)) /
     (‖PC (SC f p (0,x))‖:ℂ))
 rw [switchedChord_sides f p hf hp0 hper (x:=x) hx0 hxp]
 have hn (v:EuclideanSpace ℝ (Fin 2)) :
     PC (-v) = -(PC v):=by
   apply Complex.ext <;> simp [PC]
 rw [hn,norm_neg]
 ring
lemma exp_add_pi_neg (z:ℝ):Circle.exp (z + Real.pi) = - Circle.exp z:=by
 apply Circle.ext
 rw [Circle.coe_neg,Circle.coe_exp,Circle.coe_exp]
 have hneg:-(Complex.exp ((z:ℂ) * Complex.I)) =
     Complex.exp ((z:ℂ) * Complex.I) *
       Complex.exp ((Real.pi:ℂ) * Complex.I):=by
   rw [Complex.exp_pi_mul_I]
   ring
 rw [hneg,← Complex.exp_add]
 congr 2
 push_cast
 ring
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Boundary.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Local.lean
set_option linter.all false
namespace H
open scoped Interval Topology
open Set
section gap
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def KP (p δ:ℝ):Set (ℝ × ℝ) :=
 {q | q.1 ∈ Set.Icc (0:ℝ) p ∧ q.2 ∈ Set.Icc (0:ℝ) p ∧
     δ ≤ |q.2-q.1| ∧ |q.2-q.1| ≤ p-δ}
lemma isCompact_separatedPairs (p δ:ℝ) :
   IsCompact (KP p δ):=by
 have hbox:IsCompact (Set.Icc (0:ℝ) p ×ˢ Set.Icc (0:ℝ) p) :=
   (isCompact_Icc.prod isCompact_Icc)
 have hfun:Continuous (fun q:ℝ × ℝ => |q.2-q.1|):=by fun_prop
 have hclosed1:IsClosed {q:ℝ × ℝ | δ ≤ |q.2-q.1|} :=
   isClosed_le continuous_const hfun
 have hclosed2:IsClosed {q:ℝ × ℝ | |q.2-q.1| ≤ p-δ} :=
   isClosed_le hfun continuous_const
 have hEq:KP p δ =
     (Set.Icc (0:ℝ) p ×ˢ Set.Icc (0:ℝ) p) ∩
       ({q:ℝ × ℝ | δ ≤ |q.2-q.1|} ∩
        {q:ℝ × ℝ | |q.2-q.1| ≤ p-δ}):=by
     ext q; constructor
     · intro h
       exact ⟨⟨h.1,h.2.1⟩,⟨h.2.2.1,h.2.2.2⟩⟩
     · intro h
       exact ⟨h.1.1,h.1.2,h.2.1,h.2.2⟩
 rw [hEq]
 exact hbox.inter_right (hclosed1.inter hclosed2)
lemma nonempty_separatedPairs {p δ:ℝ} (hp:0 < p)
   (hδ:0 < δ) (hδ':2*δ ≤ p) :
   (KP p δ).Nonempty:=by
 refine ⟨(0,δ),?_⟩
 change (0:ℝ) ∈ Set.Icc 0 p ∧ δ ∈ Set.Icc 0 p ∧
     δ ≤ |δ-0| ∧ |δ-0| ≤ p-δ
 have hδp:δ ≤ p:=by linarith
 have hh:|(δ:ℝ)-0| = δ:=by rw [sub_zero,abs_of_pos hδ]
 constructor
 · exact ⟨le_rfl,le_of_lt hp⟩
 constructor
 · exact ⟨hδ.le,hδp⟩
 constructor
 · linarith [hh]
 rw [hh]
 linarith
lemma separatedPairs_ne (f:ℝ → E) {p δ:ℝ} (hp:0 < p)
   (hper:Function.Periodic f p)
   (hinj:Set.InjOn f (Set.Ico (0:ℝ) p)) (hδ:0 < δ)
   {q:ℝ × ℝ} (hq:q ∈ KP p δ) :
   f q.2 ≠ f q.1:=by
 rcases hq with ⟨hsb,htb,hlo,hhi⟩
 dsimp at hsb htb hlo hhi ⊢
 have hne:q.2 ≠ q.1:=by
   intro h
   rw [h,sub_self,abs_zero] at hlo
   linarith
 by_cases hlt:q.1 < q.2
 · have hendis:q.1 ≠ 0 ∨ q.2 ≠ p:=by
     by_contra hn
     push Not at hn
     rw [hn.1,hn.2] at hhi
     have:|p-(0:ℝ)| = p:=by rw [sub_zero,abs_of_pos hp]
     rw [this] at hhi
     linarith
   exact triangle_endpoints_ne f hp hper hinj hsb.1 hlt.le htb.2 hlt
       hendis
 · have hgt:q.2 < q.1:=lt_of_le_of_ne (le_of_not_gt hlt) hne
   have hendis:q.2 ≠ 0 ∨ q.1 ≠ p:=by
     by_contra hn
     push Not at hn
     rw [hn.1,hn.2] at hhi
     have:|(0:ℝ)-p| = p:=by rw [abs_sub_comm,sub_zero,abs_of_pos hp]
     rw [this] at hhi
     linarith
   exact (triangle_endpoints_ne f hp hper hinj htb.1 hgt.le
     hsb.2 hgt hendis) |> Ne.symm
lemma exists_pos_forall_norm_sub_of_separated
   (f:ℝ → E) (hf:Continuous f) {p δ:ℝ} (hp:0 < p)
   (hδ:0 < δ) (hδ':2*δ ≤ p)
   (hper:Function.Periodic f p)
   (hinj:Set.InjOn f (Set.Ico (0:ℝ) p)) :
   ∃ρ:ℝ,0 < ρ ∧ ∀q ∈ KP p δ,
      ρ ≤ ‖f q.2 - f q.1‖:=by
 let K:Set (ℝ × ℝ):=KP p δ
 have hK:IsCompact K:=isCompact_separatedPairs p δ
 have hKn:K.Nonempty:=nonempty_separatedPairs hp hδ hδ'
 have hnorm:Continuous (fun q:ℝ × ℝ => ‖f q.2 - f q.1‖):=by
   fun_prop
 obtain ⟨q,hq,hmin⟩:=hK.exists_isMinOn hKn hnorm.continuousOn
 refine ⟨‖f q.2 - f q.1‖,?_,?_⟩
 · have hn:=separatedPairs_ne f hp hper hinj hδ hq
   exact (norm_pos_iff.mpr (sub_ne_zero.mpr hn))
 · intro x hx
   exact hmin hx
end gap
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Local.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Semicircle.lean
set_option linter.all false
namespace H
open Set
lemma abs_endpoint_sub_lt_three_pi_of_cos_nonneg
   {B:ℝ → ℝ} {p a:ℝ}
   (hp:0 < p) (hC:Continuous B) (h0:B 0 = a)
   (hcos:Real.cos a = 0)
   (hnon:∀x ∈ Set.Icc (0:ℝ) p,0 ≤ Real.cos (B x)) :
   |B p - a| < 3 * Real.pi:=by
 have hpi:0 < Real.pi:=Real.pi_pos
 have hs:Real.sin a = 1 ∨ Real.sin a = -1:=by
   have hu:=Real.cos_sq_add_sin_sq a
   rw [hcos] at hu
   have he:(Real.sin a)^2 = 1:=by nlinarith
   exact (sq_eq_one_iff).mp he
 have h0p:(0:ℝ) ≤ p:=hp.le
 have hup:B p - a < 3 * Real.pi:=by
   by_contra hn
   have hb:a + 3*Real.pi ≤ B p:=by linarith
   rcases hs with hs | hs
   ·
     have hqcos:Real.cos (a + Real.pi/2) = -1:=by
       rw [Real.cos_add,Real.cos_pi_div_two,Real.sin_pi_div_two,hcos,hs]
       norm_num
     have hq:a + Real.pi/2 ∈ Set.Icc (B 0) (B p):=by
       rw [h0]
       constructor <;> linarith
     rcases (intermediate_value_Icc h0p hC.continuousOn hq) with
       ⟨t,ht,he⟩
     have hz:=hnon t ht
     rw [he,hqcos] at hz
     linarith
   ·
     let q:ℝ:=a + Real.pi + Real.pi/2
     have hqcos:Real.cos q = -1:=by
       dsimp [q]
       rw [Real.cos_add (a+Real.pi) (Real.pi/2),
           Real.cos_pi_div_two,Real.sin_pi_div_two]
       rw [Real.sin_add,Real.sin_pi,Real.cos_pi,hs,
           Real.cos_add,Real.cos_pi,Real.sin_pi,hcos]
       norm_num
     have hq:q ∈ Set.Icc (B 0) (B p):=by
       dsimp [q]
       rw [h0]
       constructor <;> linarith
     rcases (intermediate_value_Icc h0p hC.continuousOn hq) with
       ⟨t,ht,he⟩
     have hz:=hnon t ht
     rw [he,hqcos] at hz
     linarith
 have hlo:-(3 * Real.pi) < B p - a:=by
   by_contra hn
   have hb:B p ≤ a - 3*Real.pi:=by linarith
   rcases hs with hs | hs
   · let q:ℝ:=a - Real.pi - Real.pi/2
     have hqcos:Real.cos q = -1:=by
       dsimp [q]
       rw [Real.cos_sub (a-Real.pi) (Real.pi/2),
           Real.cos_pi_div_two,Real.sin_pi_div_two]
       rw [Real.sin_sub,Real.sin_pi,Real.cos_pi,hs,
           Real.cos_sub,Real.cos_pi,Real.sin_pi,hcos]
       norm_num
     have hq:q ∈ Set.Icc (B p) (B 0):=by
       dsimp [q]
       rw [h0]
       constructor <;> linarith
     rcases (intermediate_value_Icc' h0p hC.continuousOn hq) with
       ⟨t,ht,he⟩
     have hz:=hnon t ht
     rw [he,hqcos] at hz
     linarith
   · have hqcos:Real.cos (a - Real.pi/2) = -1:=by
       rw [Real.cos_sub,Real.cos_pi_div_two,Real.sin_pi_div_two,hcos,hs]
       norm_num
     have hq:a - Real.pi/2 ∈ Set.Icc (B p) (B 0):=by
       rw [h0]
       constructor <;> linarith
     rcases (intermediate_value_Icc' h0p hC.continuousOn hq) with
       ⟨t,ht,he⟩
     have hz:=hnon t ht
     rw [he,hqcos] at hz
     linarith
 exact (abs_lt).2 ⟨by simpa using hlo,hup⟩
end H
namespace H
lemma odd_pi_abs_lt_three {k:ℤ}
   (h:|(((2*k+1:ℤ):ℝ)) * Real.pi| < 3 * Real.pi) :
   k = 0 ∨ k = -1:=by
 have hp:0 < Real.pi:=Real.pi_pos
 have hh:=(abs_lt.mp h)
 have hu:(((2*k+1:ℤ):ℝ)) < 3:=by nlinarith
 have hl:(-3:ℝ) < (((2*k+1:ℤ):ℝ)):=by nlinarith
 have hur:((k:ℤ):ℝ) < 1:=by
   push_cast at hu
   linarith
 have hlr:(-2:ℝ) < ((k:ℤ):ℝ):=by
   push_cast at hl
   linarith
 have hu':k < (1:ℤ):=by exact_mod_cast hur
 have hl':(-2:ℤ) < k:=by exact_mod_cast hlr
 omega
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Semicircle.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Cone.lean
set_option linter.all false
namespace H
open scoped Interval Topology
open Set
variable {F:Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
lemma inner_pos_of_norm_sub_lt_one {v w:F}
   (hv:‖v‖ = 1) (h:‖w-v‖ < 1) :
   0 < @inner ℝ F _ v w:=by
 have hnorm:=abs_real_inner_le_norm v (w-v)
 have hlower:-(1:ℝ) < @inner ℝ F _ v (w-v):=by
   have habs:|@inner ℝ F _ v (w-v)| < 1:=by
     calc
       |@inner ℝ F _ v (w-v)| ≤ ‖v‖ * ‖w-v‖:=hnorm
       _ = ‖w-v‖:=by rw [hv]; ring
       _ < 1:=h
   exact (abs_lt.mp habs).1
 have hid:@inner ℝ F _ v w = @inner ℝ F _ v v + @inner ℝ F _ v (w-v):=by
   rw [inner_sub_right]
   ring
 rw [hid,real_inner_self_eq_norm_sq,hv]
 norm_num
 linarith
lemma inner_chord_pos_of_deriv_close
   [CompleteSpace F] (f:ℝ → F) (hf:ContDiff ℝ 1 f)
   (v:F) (hv:‖v‖ = 1) {A B s t:ℝ}
   (hs:s ∈ Set.Icc A B) (ht:t ∈ Set.Icc A B) (hst:s < t)
   (hclose:∀x ∈ Set.Icc A B,‖deriv f x - v‖ < (1:ℝ)) :
   0 < @inner ℝ F _ v (f t - f s):=by
 have hpos:0 < t-s:=sub_pos.mpr hst
 have hseg (u:ℝ) (hu:u ∈ Set.Icc (0:ℝ) 1) :
     (t-s)*u+s ∈ Set.Icc A B:=by
   constructor
   · have hu0:=hu.1
     have hmul0:0 ≤ (t-s)*u:=mul_nonneg hpos.le hu0
     linarith [hs.1]
   · have hu1:=hu.2
     have hmul:(t-s)*u ≤ (t-s)*1 :=
       mul_le_mul_of_nonneg_left hu1 hpos.le
     nlinarith [ht.2]
 let g:ℝ → ℝ:=fun u => ‖deriv f ((t-s)*u+s) - v‖
 have gC:Continuous g:=by
   have hd:Continuous (deriv f):=hf.continuous_deriv (by norm_num)
   fun_prop
 obtain ⟨u,hu,huMax⟩:=(isCompact_Icc.exists_isMaxOn
     (show (Set.Icc (0:ℝ) 1).Nonempty from ⟨0,by norm_num⟩)
     gC.continuousOn)
 have gu1:g u < 1:=hclose _ (hseg u hu)
 have gbd (z:ℝ) (hz:z ∈ Set.uIcc (0:ℝ) 1) :
     ‖deriv f ((t-s)*z+s) - v‖ ≤ g u:=by
   have hi:z ∈ Set.Icc (0:ℝ) 1:=by simpa using hz
   exact huMax hi
 have hc:IntervalIntegrable (fun _z:ℝ => v)
     MeasureTheory.MeasureSpace.volume 0 1 :=
     (continuous_const:Continuous (fun _z:ℝ => v)).continuousOn.intervalIntegrable
 have hdcont:Continuous (fun z:ℝ => deriv f ((t-s)*z+s)):=by
   have hd:Continuous (deriv f):=hf.continuous_deriv (by norm_num)
   fun_prop
 have hdint:IntervalIntegrable (fun z:ℝ => deriv f ((t-s)*z+s))
     MeasureTheory.MeasureSpace.volume 0 1:=hdcont.continuousOn.intervalIntegrable
 have hnormmean:‖MV f s (t-s) - v‖ ≤ g u:=by
   have hvconst:(∫ _z in (0:ℝ)..1,v) = v:=by
     simpa using (intervalIntegral.integral_const (a:=(0:ℝ)) (b:=1) v)
   have heq:MV f s (t-s) - v =
         ∫ z in (0:ℝ)..1,(deriv f ((t-s)*z+s) - v):=by
     unfold MV
     rw [intervalIntegral.integral_sub hdint hc,hvconst]
   rw [heq]
   exact (intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(0:ℝ)) (b:=1)
      (f:=fun z:ℝ => deriv f ((t-s)*z+s) - v)
      (by intro z hz; exact gbd z (Set.uIoc_subset_uIcc hz))) |>.trans_eq
       (by simp)
 have hmdir:0 < @inner ℝ F _ v (MV f s (t-s)) :=
   inner_pos_of_norm_sub_lt_one hv (lt_of_le_of_lt hnormmean gu1)
 have hmul:=smul_meanVelocity f hf s (t-s)
 have he:(t-s) • MV f s (t-s) = f t - f s:=by
   simpa using hmul
 rw [← he]
 simp [real_inner_smul_right,hmdir,mul_pos hpos hmdir]
end H
namespace H
open Set
variable {F:Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
lemma affine_edges_ne_of_deriv_close
   (f:ℝ → F) (hf:ContDiff ℝ 1 f)
   (v:F) (hv:‖v‖ = 1) {A B a b c d l m:ℝ}
   (ha:a ∈ Set.Icc A B) (hb:b ∈ Set.Icc A B)
   (hc:c ∈ Set.Icc A B) (hd:d ∈ Set.Icc A B)
   (hab:a < b) (hbc:b ≤ c) (hcd:c < d)
   (hl0:0 ≤ l) (hl1:l < 1) (hm0:0 ≤ m) (hm1:m ≤ 1)
   (hclose:∀x ∈ Set.Icc A B,‖deriv f x - v‖ < (1:ℝ)) :
   f a + l • (f b - f a) ≠ f c + m • (f d - f c):=by
 let L:F → ℝ:=fun x => @inner ℝ F _ v x
 have hab':0 < L (f b) - L (f a):=by
   have h:=inner_chord_pos_of_deriv_close f hf v hv ha hb hab hclose
   dsimp [L]
   rw [inner_sub_right] at h
   exact h
 have hcd':0 < L (f d) - L (f c):=by
   have h:=inner_chord_pos_of_deriv_close f hf v hv hc hd hcd hclose
   dsimp [L]
   rw [inner_sub_right] at h
   exact h
 have hbc':L (f b) ≤ L (f c):=by
   rcases hbc.eq_or_lt with he | he
   · simp [he]
   · exact (by
       have hh:=inner_chord_pos_of_deriv_close f hf v hv hb hc he hclose
       dsimp [L]
       rw [inner_sub_right] at hh
       linarith)
 have heval (x y:F) (z:ℝ):L (x + z • (y-x)) =
         L x + z * (L y - L x):=by
   dsimp [L]
   rw [inner_add_right,real_inner_smul_right,inner_sub_right]
 intro hEq
 have hsc:=congrArg L hEq
 rw [heval,heval] at hsc
 nlinarith
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Cone.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/SupportBase.lean
set_option linter.all false
namespace H
open scoped Topology Interval
open Set
lemma injOn_shift_Ico {E:Type*} (f:ℝ → E) {p s:ℝ} (hp:0 < p)
    (hs0:0 ≤ s) (hsp:s < p) (hper:Function.Periodic f p)
    (inj:Set.InjOn f (Set.Ico (0:ℝ) p)) :
    Set.InjOn (fun t:ℝ => f (t+s)) (Set.Ico (0:ℝ) p):=by
  intro x hx y hy he
  let red:ℝ → ℝ:=fun t => if p ≤ t+s then t+s-p else t+s
  have hrmem:∀t ∈ Set.Ico (0:ℝ) p,red t ∈ Set.Ico (0:ℝ) p:=by
    intro t ht
    dsimp [red]
    split_ifs with h
    · constructor <;> linarith [ht.2]
    · constructor <;> linarith [ht.1]
  have hfred:∀t ∈ Set.Ico (0:ℝ) p,f (t+s) = f (red t):=by
    intro t ht
    dsimp [red]
    split_ifs with h
    · have hq:=hper (t+s-p)
      have eqn:(t+s-p)+p = t+s:=by ring
      rw [eqn] at hq
      exact hq
    · rfl
  have er:red x = red y:=by
    apply inj (hrmem x hx) (hrmem y hy)
    rw [← hfred x hx,← hfred y hy]
    exact he
  dsimp [red] at er
  split_ifs at er with h1 h2
  · linarith
  · exfalso; have:=hx.2; have:=hy.1; linarith
  · exfalso; have:=hy.2; have:=hx.1; linarith
  · linarith
lemma lift_cos_nonneg_of_re {v:EuclideanSpace ℝ (Fin 2)} {z:ℝ}
    (hv: v ≠ 0)
    (he:Circle.exp z = TC (PC v)
      ((planeComplex_eq_zero_iff _).not.mpr hv))
    (hre:0 ≤ v 0):0 ≤ Real.cos z:=by
  have he':=congrArg (fun w:Circle => (w:ℂ)) he
  change Complex.exp ((z:ℂ)*Complex.I) = _ at he'
  have her:=congrArg Complex.re he'
  have hnon:PC v ≠ 0 :=
    (planeComplex_eq_zero_iff _).not.mpr hv
  have hpos:0 < ‖PC v‖:=norm_pos_iff.mpr hnon
  have hform:Real.cos z = v 0 / ‖PC v‖:=by
    simpa [Complex.exp_re,coe_toCircle,PC] using her
  rw [hform]
  exact div_nonneg hre (le_of_lt hpos)
lemma switchedChord_left_re_nonneg (f:ℝ → EuclideanSpace ℝ (Fin 2))
    (hf:ContDiff ℝ 1 f) {p:ℝ} (hp:0<p) (per:Function.Periodic f p)
    (hmin:∀x ∈ Set.Icc (0:ℝ) p,f 0 0 ≤ f x 0)
    (hv0:deriv f 0 0 = 0) {x:ℝ} (hx0:0≤x) (hxp:x≤p) :
    0 ≤ (SC f p (0,x)) 0:=by
  by_cases hz:x = 0
  · subst x
    have hh:(0:ℝ) ≤ p/2:=by linarith
    simp [SC,hh,meanVelocity_zero,
      hf.differentiable (by exact one_ne_zero),hv0]
  by_cases he:x = p
  · subst x
    have hh:¬ (p-0 ≤ p/2):=by linarith
    have hzarg:(p-0)-p = 0:=by ring
    have hnp:¬ p ≤ p/2:=by linarith
    simp [SC,hnp,meanVelocity_zero,
      hf.differentiable (by exact one_ne_zero),hv0]
  ·
    have hxpos:0 < x:=lt_of_le_of_ne hx0 (Ne.symm hz)
    have hxlt:x < p:=lt_of_le_of_ne hxp he
    by_cases hs:x ≤ p/2
    · simp [SC,hs]
      have hsm:=congrArg (fun v:EuclideanSpace ℝ (Fin 2) => v 0)
         (smul_meanVelocity f hf 0 x)
      have hproj:=hmin x ⟨hxpos.le,hxlt.le⟩
      simp at hsm
      have:0 ≤ (MV f 0 x) 0:=by nlinarith
      simpa using this
    ·
      have hsm:=congrArg (fun v:EuclideanSpace ℝ (Fin 2) => v 0)
         (neg_smul_meanVelocity_sub_period f hf per 0 x)
      have hproj:=hmin x ⟨hxpos.le,hxlt.le⟩
      simp at hsm
      have hpcoef:0 < p - x:=by linarith
      have hn:0 ≤ - (MV f 0 (x-p)) 0:=by nlinarith
      simpa [SC,hs] using hn
theorem tangent_turn_support_pm
 (f:ℝ → EuclideanSpace ℝ (Fin 2)) (a:ℝ → ℝ) {p:ℝ}
 (hp0:0 < p) (hf:ContDiff ℝ 1 f) (haC:Continuous a)
 (hper:Function.Periodic f p) (hinj:Set.InjOn f (Set.Ico (0:ℝ) p))
 (ha:∀x,deriv f x = !₂[Real.cos (a x),Real.sin (a x)])
 (hmin:∀x ∈ Set.Icc (0:ℝ) p,f 0 0 ≤ f x 0)
 (hv0:deriv f 0 0 = 0) :
 ∃k:ℤ,(k = 0 ∨ k = -1) ∧
      a p - a 0 = ((2*k+1:ℤ):ℝ) * (2*Real.pi):=by
  classical
  have hv:∀x:ℝ,deriv f x ≠ 0:=by
    intro x
    rw [ha]
    intro h
    have hcos:=congrArg (fun v:EuclideanSpace ℝ (Fin 2) => v 0) h
    have hsin:=congrArg (fun v:EuclideanSpace ℝ (Fin 2) => v 1) h
    have hc:Real.cos (a x) = 0:=by simpa using hcos
    have hs:Real.sin (a x) = 0:=by simpa using hsin
    have hunit:=Real.cos_sq_add_sin_sq (a x)
    rw [hc,hs] at hunit
    norm_num at hunit
  obtain ⟨b,hb0,hb⟩:=exists_chord_lift f p hf hp0 hper hinj hv (a 0) (ha 0)
  let u:ℝ → ℝ:=fun x => max 0 (min p x)
  have hucont:Continuous u:=by dsimp [u]; fun_prop
  have hu0 (x:ℝ):0 ≤ u x:=by
    dsimp [u]; exact le_max_left _ _
  have hup (x:ℝ):u x ≤ p:=by
    dsimp [u]; exact max_le (le_of_lt hp0) (min_le_left _ _)
  have uzero:u 0 = 0:=by simp [u,le_of_lt hp0]
  have up:u p = p:=by simp [u,le_of_lt hp0]
  let D:ℝ → CT p:=fun x =>
    ⟨(u x,u x),⟨hu0 x,le_rfl,hup x⟩⟩
  let L:ℝ → CT p:=fun x =>
    ⟨(0,u x),⟨le_rfl,hu0 x,hup x⟩⟩
  let R:ℝ → CT p:=fun x =>
    ⟨(u x,p),⟨hu0 x,hup x,le_rfl⟩⟩
  have hDc:Continuous D:=by
    apply Continuous.subtype_mk
    exact hucont.prodMk hucont
  have hLc:Continuous L:=by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk hucont
  have hRc:Continuous R:=by
    apply Continuous.subtype_mk
    exact hucont.prodMk continuous_const
  let T:ℝ:=2 * Real.pi
  have hT:T ≠ 0:=by dsimp [T]; positivity
  let gd:ℝ → ℝ:=fun x => (b (D x) - a (u x)) / T
  have gdC:Continuous gd:=by
    dsimp [gd]
    exact ((b.continuous.comp hDc).sub (haC.comp hucont)).div_const _
  have gdZ:∀x,∃n:ℤ,gd x = (n:ℝ):=by
    intro x
    have hd:=hb (D x)
    have he:Circle.exp (b (D x)) = Circle.exp (a (u x)) :=
      hd.trans (chordCircle_diagonal f p hf hp0 hper hinj hv a ha
        (hu0 x) (hup x))
    obtain ⟨n,hn⟩:=Circle.exp_eq_exp.mp he
    refine ⟨n,?_⟩
    dsimp [gd,T]
    rw [hn]
    field_simp
    <;> ring
  have gdconst:=continuous_integer_constant gd gdC gdZ
  have hdiag:b (D p) = a p:=by
    have h:=gdconst p
    have hz:gd 0 = 0:=by
      dsimp [gd,D]
      simp [uzero,hb0]
    rw [hz] at h
    dsimp [gd] at h
    rw [up] at h
    exact sub_eq_zero.mp (div_eq_zero_iff.mp h |>.resolve_right hT)
  let gs:ℝ → ℝ:=fun x => (b (R x) - b (L x) - Real.pi) / T
  have gsC:Continuous gs:=by
    dsimp [gs]
    exact (((b.continuous.comp hRc).sub (b.continuous.comp hLc)).sub
      continuous_const).div_const _
  have gsZ:∀x,∃n:ℤ,gs x = (n:ℝ):=by
    intro x
    have hside0:=hb (R x)
    have hside1:=hb (L x)
    have hside:=chordCircle_sides f p hf hp0 hper hinj hv
      (hu0 x) (hup x)
    have hexp:Circle.exp (b (R x)) = Circle.exp (b (L x) + Real.pi):=by
      calc
        Circle.exp (b (R x)) = _:=hside0
        _ = - chordCircle f p hf hp0 hper hinj hv (L x):=hside
        _ = - Circle.exp (b (L x)):=congrArg Neg.neg hside1.symm
        _ = _:=(exp_add_pi_neg _).symm
    obtain ⟨n,hn⟩:=Circle.exp_eq_exp.mp hexp
    refine ⟨n,?_⟩
    dsimp [gs,T]
    rw [hn]
    field_simp
    <;> ring
  have gsconst:=continuous_integer_constant gs gsC gsZ
  obtain ⟨k,hk⟩:=gsZ 0
  have hturn:a p - a 0 = ((2*k+1:ℤ):ℝ) * (2*Real.pi):=by
    have heq:=gsconst p
    rw [hk] at heq
    dsimp [gs] at heq
    dsimp [R,L] at heq
    simp [uzero,up] at heq
    have hR0:b (⟨(0,p),by exact ⟨le_rfl,le_of_lt hp0,le_rfl⟩⟩:CT p) =
          b (R 0):=by congr 2 <;> simp [R,uzero]
    have hb00:b (L 0) = a 0:=by simpa [L,uzero] using hb0
    have hbpp:b (R p) = a p:=by simpa [R,up,D] using hdiag
    have heq' :
        (b (R p) - b (L p) - Real.pi) / T = (k:ℝ):=by
      have hh:=gsconst p
      rw [hk] at hh
      exact hh
    have heq0 :
        (b (R 0) - b (L 0) - Real.pi) / T = (k:ℝ):=by
      exact hk
    have hLpR0:L p = R 0:=by
      apply Subtype.ext
      simp [L,R,up,uzero]
    have hs0:b (L 0) = a 0:=by simpa [L,uzero] using hb0
    have hsp:b (R p) = a p:=by simpa [R,up,D] using hdiag
    rw [hLpR0] at heq'
    rw [hsp] at heq'
    rw [hs0] at heq0
    dsimp [T] at heq' heq0 ⊢
    have hpi:(2*Real.pi:ℝ) ≠ 0:=by positivity
    field_simp at heq' heq0
    push_cast at heq' heq0 ⊢
    linarith
  have hs0:b (L 0) = a 0:=by simpa [L,uzero] using hb0
  have hLpR0:L p = R 0:=by
    apply Subtype.ext
    simp [L,R,up,uzero]
  have heq0 :
      (b (R 0) - b (L 0) - Real.pi) / T = (k:ℝ):=by exact hk
  have hsideval:b (L p) - a 0 = (((2*k+1:ℤ):ℝ)) * Real.pi:=by
    rw [hLpR0]
    rw [hs0] at heq0
    dsimp [T] at heq0
    field_simp at heq0
    push_cast at heq0 ⊢
    linarith
  have hcosa0:Real.cos (a 0) = 0:=by
    have hh:=congrArg (fun v:EuclideanSpace ℝ (Fin 2) => v 0) (ha 0)
    simpa [hv0] using hh.symm
  let B:ℝ → ℝ:=fun x => b (L x)
  have hBC:Continuous B:=b.continuous.comp hLc
  have hcosB:∀x ∈ Set.Icc (0:ℝ) p,0 ≤ Real.cos (B x):=by
    intro x hx
    have hleft:=switchedChord_left_re_nonneg f hf hp0 hper hmin hv0 hx.1 hx.2
    have hne:=switchedChord_ne_zero f hf hp0 hper hinj hv (L x)
    have hexp:=hb (L x)
    have hux:u x = x:=by simp [u,hx.1,hx.2]
    have hleft':0 ≤ (SC f p (L x).1) 0:=by
      simpa [L,hux] using hleft
    exact lift_cos_nonneg_of_re hne hexp hleft'
  have hB0:B 0 = a 0:=by simpa [B,L,uzero] using hb0
  have hbound:=abs_endpoint_sub_lt_three_pi_of_cos_nonneg
      (B:=B) hp0 hBC hB0 hcosa0 hcosB
  have hnum:|(((2*k+1:ℤ):ℝ)) * Real.pi| < 3*Real.pi:=by
    simpa [B,hsideval] using hbound
  have hor:=odd_pi_abs_lt_three hnum
  exact ⟨k,hor,hturn⟩
end H
namespace H
lemma deriv0_coord_of_left_support (g:ℝ → EuclideanSpace ℝ (Fin 2)) {p:ℝ}
 (hp:0<p) (hg:ContDiff ℝ 1 g) (hper:Function.Periodic g p)
 (hmin:∀x ∈ Set.Icc (0:ℝ) p,g 0 0 ≤ g x 0) :
 (deriv g 0) 0 = 0:=by
 let X:ℝ → ℝ:=fun t => g t 0
 have hall:∀t ∈ Set.Icc (-p) p,X 0 ≤ X t:=by
  intro t ht
  by_cases hh:0 ≤ t
  · exact hmin t ⟨hh,ht.2⟩
  · have ht':t+p ∈ Set.Icc (0:ℝ) p:=⟨by linarith [ht.1],by linarith⟩
    have hm:=hmin (t+p) ht'
    have hp':=hper t
    simpa [X,hp'] using hm
 have hloc:IsLocalMin X 0:=by
   have hset:Set.Icc (-p) p ∈ (nhds (0:ℝ)):=by
     have hopen:Set.Ioo (-p) p ∈ (nhds (0:ℝ)):=Ioo_mem_nhds (by linarith) (by linarith)
     exact Filter.mem_of_superset hopen (by intro y hy; exact ⟨le_of_lt hy.1,le_of_lt hy.2⟩)
   exact Filter.mem_of_superset hset hall
 have hder:HasDerivAt X ((deriv g 0) 0) 0:=by
   have hu:HasDerivAt g (deriv g 0) 0 :=
      (hg.differentiable (by exact one_ne_zero)).differentiableAt.hasDerivAt
   let P:EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
      EuclideanSpace.proj 0
   have hpost:=P.hasFDerivAt.comp_hasDerivAt 0 hu
   simpa [X,P,Function.comp_def] using hpost
 have hh:=hloc.deriv_eq_zero
 rw [hder.deriv] at hh
 exact hh
end H
namespace H
lemma exists_left_support_shift (f:ℝ → EuclideanSpace ℝ (Fin 2)) {p:ℝ}
 (hp:0<p) (hf:ContDiff ℝ 1 f) (hper: Function.Periodic f p) :
 ∃s:ℝ,0 ≤ s ∧ s < p ∧ ∀x ∈ Set.Icc (0:ℝ) p,
              f s 0 ≤ f (x+s) 0:=by
 let X:ℝ → ℝ:=fun t => f t 0
 have hxc:Continuous X:=by dsimp [X]; fun_prop
 obtain ⟨s,hs,hm⟩:=(isCompact_Icc.exists_isMinOn
   (show (Set.Icc (0:ℝ) p).Nonempty by exact ⟨0,le_rfl,hp.le⟩) hxc.continuousOn)
 by_cases hend:s = p
 · subst s
   refine ⟨0,le_rfl,hp,?_⟩
   intro x hx
   have hmin:=hm hx
   have h0p:f 0 = f p:=by simpa using (hper 0).symm
   dsimp [X] at hmin
   rw [h0p]
   simpa using hmin
 · have hslt:s < p:=lt_of_le_of_ne hs.2 hend
   refine ⟨s,hs.1,hslt,?_⟩
   intro x hx
   by_cases hw:x+s ≤ p
   · have hnon:0 ≤ x+s:=by linarith [hs.1,hx.1]
     have hmin:=hm ⟨hnon,hw⟩
     simpa [X] using hmin
   · have hy:x+s-p ∈ Set.Icc (0:ℝ) p:=by
        constructor
        · linarith
        · linarith [hx.2,hslt]
     have hmin:=hm hy
     dsimp [X] at hmin
     have hh:=hper (x+s-p)
     have he:(x+s-p)+p = x+s:=by ring
     rw [he] at hh
     rw [hh]
     exact hmin
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/SupportBase.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Metric.lean
set_option linter.all false
namespace H
open scoped Interval Topology
open Set
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma norm_sub_le_mul_sub_of_deriv_le
   (f:ℝ → E) (hf:ContDiff ℝ 1 f) {s t M:ℝ}
   (hst:s ≤ t) (hM:∀x ∈ Set.Icc s t,‖deriv f x‖ ≤ M) :
   ‖f t - f s‖ ≤ M * (t-s):=by
 have hFTC:=integral_deriv_contDiff_one f hf s t
 rw [← hFTC]
 have h:=intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=s) (b:=t) (C:=M) (f:=fun x:ℝ => deriv f x)
    (by
      intro x hx
      have hui:x ∈ Set.uIcc s t:=Set.uIoc_subset_uIcc hx
      rw [Set.uIcc_of_le hst] at hui
      exact hM x hui)
 rw [abs_of_nonneg (sub_nonneg.mpr hst)] at h
 exact h
lemma one_lipschitz_of_deriv_norm_one
   (f:ℝ → E) (hf:ContDiff ℝ 1 f)
   (hunit:∀x:ℝ,‖deriv f x‖ = 1) {s t:ℝ} :
   ‖f t - f s‖ ≤ |t-s|:=by
 by_cases h:s ≤ t
 · have hh:=norm_sub_le_mul_sub_of_deriv_le f hf h
       (M:=(1:ℝ)) (by intro x hx; rw [hunit x])
   simpa [abs_of_nonneg (sub_nonneg.mpr h)] using hh
 · have h':t ≤ s:=le_of_not_ge h
   have hh:=norm_sub_le_mul_sub_of_deriv_le f hf h'
       (M:=(1:ℝ)) (s:=t) (t:=s)
       (by intro x hx; rw [hunit x])
   rw [norm_sub_rev] at hh
   simpa [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr h')] using hh
end H
namespace H
open Set
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma exists_uniform_deriv_close_on_Icc
   (f:ℝ → E) (hf:ContDiff ℝ 1 f) {A B ε:ℝ} (hε:0 < ε) :
   ∃d:ℝ,0 < d ∧
     ∀x ∈ Set.Icc A B,∀y ∈ Set.Icc A B,
       |x-y| < d → ‖deriv f x - deriv f y‖ < ε:=by
 have hC:Continuous (deriv f):=hf.continuous_deriv (by norm_num)
 have hu:UniformContinuousOn (deriv f) (Set.Icc A B) :=
   isCompact_Icc.uniformContinuousOn_of_continuous hC.continuousOn
 rcases (Metric.uniformContinuousOn_iff.mp hu ε hε) with ⟨d,hd,H⟩
 refine ⟨d,hd,?_⟩
 intro x hx y hy hxy
 simpa [Real.dist_eq,dist_eq_norm] using (H x hx y hy (by simpa [Real.dist_eq] using hxy))
end H
namespace H
open Set
variable {F:Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
lemma exists_period_cone_window
   (f:ℝ → F) {p:ℝ} (hp:0 < p)
   (hf:ContDiff ℝ 1 f) (hper:Function.Periodic f p)
   (hunit:∀x:ℝ,‖deriv f x‖ = 1) :
   ∃d:ℝ,0 < d ∧ d < p/2 ∧
     ∀u ∈ Set.Icc (-p) (2*p),∀x ∈ Set.Icc (-p) (2*p),|x-u| < d → ‖deriv f u‖ = 1 ∧ ‖deriv f x - deriv f u‖ < 1:=by
 obtain ⟨d0,hd0,hmod⟩ :=
   exists_uniform_deriv_close_on_Icc (E:=F) f hf (A:=-p) (B:=2*p)
     (ε:=(1:ℝ)) (by norm_num)
 let d:=min d0 (p/4)
 have hdp4:0 < p/4:=by positivity
 have hd:0 < d:=lt_min hd0 hdp4
 have hd':d < p/2:=lt_of_le_of_lt (min_le_right _ _) (by linarith)
 refine ⟨d,hd,hd',?_⟩
 intro u hu x hx hxu
 refine ⟨hunit u,?_⟩
 have hdu:|x-u| < d0:=lt_of_lt_of_le hxu (min_le_left _ _)
 exact hmod x hx u hu hdu
end H
namespace H
open Set
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma affine_ne_of_gap
   {P Q P' Q':E} {gap R S:ℝ}
   (hgap:gap ≤ ‖Q - P‖)
   (hR:‖P' - P‖ ≤ R) (hS:‖Q' - Q‖ ≤ S)
   (hstrict:R + S < gap):P' ≠ Q':=by
 intro h
 subst Q'
 have heq:Q - P = (Q - P') + (P' - P):=by abel
 have ht:‖Q - P‖ ≤ ‖Q - P'‖ + ‖P' - P‖:=by
   rw [heq]
   exact norm_add_le _ _
 rw [norm_sub_rev Q P'] at ht
 linarith
lemma norm_affine_sub_left_le
   (P Q:E) {l:ℝ} (hl0:0 ≤ l) (hl1:l ≤ 1) :
   ‖(P + l • (Q-P)) - P‖ ≤ ‖Q-P‖:=by
 have hcalc:(P + l • (Q-P)) - P = l • (Q-P):=by abel
 rw [hcalc,norm_smul,Real.norm_eq_abs,abs_of_nonneg hl0]
 exact mul_le_of_le_one_left (norm_nonneg _) hl1
lemma affine_edges_ne_of_parameter_gap
   [CompleteSpace E]
   (f:ℝ → E) (hf:ContDiff ℝ 1 f)
   (hunit:∀x:ℝ,‖deriv f x‖ = 1)
   {p δ ρ a b c d l m L:ℝ}
   (hgap:∀q ∈ KP p δ,ρ ≤ ‖f q.2 - f q.1‖)
   (habp:a ∈ Set.Icc (0:ℝ) p) (hacp:c ∈ Set.Icc (0:ℝ) p)
   (hsep0:δ ≤ |c-a|) (hsep1:|c-a| ≤ p-δ)
   (hab:a ≤ b) (hcd:c ≤ d)
   (hblen:b-a ≤ L) (hdlen:d-c ≤ L) (hL:2*L < ρ)
   (hl0:0 ≤ l) (hl1:l ≤ 1) (hm0:0 ≤ m) (hm1:m ≤ 1) :
   f a + l • (f b - f a) ≠ f c + m • (f d - f c):=by
 have hpair:(a,c) ∈ KP p δ :=
   ⟨habp,hacp,by simpa using hsep0,by simpa using hsep1⟩
 have hgap':ρ ≤ ‖f c - f a‖:=hgap (a,c) hpair
 have hlen1:‖f b - f a‖ ≤ L:=by
   calc
     ‖f b - f a‖ ≤ |b-a|:=one_lipschitz_of_deriv_norm_one f hf hunit
     _ ≤ L:=by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; exact hblen
 have hlen2:‖f d - f c‖ ≤ L:=by
   calc
     ‖f d - f c‖ ≤ |d-c|:=one_lipschitz_of_deriv_norm_one f hf hunit
     _ ≤ L:=by rw [abs_of_nonneg (sub_nonneg.mpr hcd)]; exact hdlen
 have hstep1:‖(f a + l • (f b - f a)) - f a‖ ≤ L :=
    le_trans (norm_affine_sub_left_le (f a) (f b) hl0 hl1) hlen1
 have hstep2:‖(f c + m • (f d - f c)) - f c‖ ≤ L :=
    le_trans (norm_affine_sub_left_le (f c) (f d) hm0 hm1) hlen2
 exact affine_ne_of_gap hgap' hstep1 hstep2 (by linarith)
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Metric.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Orientation.lean
set_option linter.all false
namespace H
open scoped Topology Interval
open Set
theorem left_support_sin_one_of_turn_neg
 (f:ℝ → EuclideanSpace ℝ (Fin 2)) (a:ℝ → ℝ) {p:ℝ}
 (hp0:0 < p) (hf:ContDiff ℝ 1 f) (haC:Continuous a)
 (hper:Function.Periodic f p) (hinj:Set.InjOn f (Set.Ico (0:ℝ) p))
 (ha:∀x,deriv f x = !₂[Real.cos (a x),Real.sin (a x)])
 (hmin:∀x ∈ Set.Icc (0:ℝ) p,f 0 0 ≤ f x 0)
 (hv0:deriv f 0 0 = 0)
 (hneg:a p - a 0 = -(2*Real.pi)) :
 Real.sin (a 0) = 1:=by
 classical
 have hv:∀x:ℝ,deriv f x ≠ 0:=by
   intro x
   rw [ha]
   intro h
   have hcos:=congrArg (fun v:EuclideanSpace ℝ (Fin 2) => v 0) h
   have hsin:=congrArg (fun v:EuclideanSpace ℝ (Fin 2) => v 1) h
   have hc:Real.cos (a x) = 0:=by simpa using hcos
   have hs:Real.sin (a x) = 0:=by simpa using hsin
   have hunit:=Real.cos_sq_add_sin_sq (a x)
   rw [hc,hs] at hunit
   norm_num at hunit
 obtain ⟨b,hb0,hb⟩:=exists_chord_lift f p hf hp0 hper hinj hv (a 0) (ha 0)
 let u:ℝ → ℝ:=fun x => max 0 (min p x)
 have hucont:Continuous u:=by dsimp [u]; fun_prop
 have hu0 (x:ℝ):0 ≤ u x:=by
   dsimp [u]; exact le_max_left _ _
 have hup (x:ℝ):u x ≤ p:=by
   dsimp [u]; exact max_le (le_of_lt hp0) (min_le_left _ _)
 have uzero:u 0 = 0:=by simp [u,le_of_lt hp0]
 have up:u p = p:=by simp [u,le_of_lt hp0]
 let D:ℝ → CT p:=fun x =>
   ⟨(u x,u x),⟨hu0 x,le_rfl,hup x⟩⟩
 let L:ℝ → CT p:=fun x =>
   ⟨(0,u x),⟨le_rfl,hu0 x,hup x⟩⟩
 let R:ℝ → CT p:=fun x =>
   ⟨(u x,p),⟨hu0 x,hup x,le_rfl⟩⟩
 have hDc:Continuous D:=by
   apply Continuous.subtype_mk
   exact hucont.prodMk hucont
 have hLc:Continuous L:=by
   apply Continuous.subtype_mk
   exact continuous_const.prodMk hucont
 have hRc:Continuous R:=by
   apply Continuous.subtype_mk
   exact hucont.prodMk continuous_const
 let T:ℝ:=2 * Real.pi
 have hT:T ≠ 0:=by dsimp [T]; positivity
 let gd:ℝ → ℝ:=fun x => (b (D x) - a (u x)) / T
 have gdC:Continuous gd:=by
   dsimp [gd]
   exact ((b.continuous.comp hDc).sub (haC.comp hucont)).div_const _
 have gdZ:∀x,∃n:ℤ,gd x = (n:ℝ):=by
   intro x
   have hd:=hb (D x)
   have he:Circle.exp (b (D x)) = Circle.exp (a (u x)) :=
     hd.trans (chordCircle_diagonal f p hf hp0 hper hinj hv a ha
       (hu0 x) (hup x))
   obtain ⟨n,hn⟩:=Circle.exp_eq_exp.mp he
   refine ⟨n,?_⟩
   dsimp [gd,T]
   rw [hn]
   field_simp
   <;> ring
 have gdconst:=continuous_integer_constant gd gdC gdZ
 have hdiag:b (D p) = a p:=by
   have h:=gdconst p
   have hz:gd 0 = 0:=by
     dsimp [gd,D]
     simp [uzero,hb0]
   rw [hz] at h
   dsimp [gd] at h
   rw [up] at h
   exact sub_eq_zero.mp (div_eq_zero_iff.mp h |>.resolve_right hT)
 let gs:ℝ → ℝ:=fun x => (b (R x) - b (L x) - Real.pi) / T
 have gsC:Continuous gs:=by
   dsimp [gs]
   exact (((b.continuous.comp hRc).sub (b.continuous.comp hLc)).sub
     continuous_const).div_const _
 have gsZ:∀x,∃n:ℤ,gs x = (n:ℝ):=by
   intro x
   have hside0:=hb (R x)
   have hside1:=hb (L x)
   have hside:=chordCircle_sides f p hf hp0 hper hinj hv
     (hu0 x) (hup x)
   have hexp:Circle.exp (b (R x)) = Circle.exp (b (L x) + Real.pi):=by
     calc
       Circle.exp (b (R x)) = _:=hside0
       _ = - chordCircle f p hf hp0 hper hinj hv (L x):=hside
       _ = - Circle.exp (b (L x)):=congrArg Neg.neg hside1.symm
       _ = _:=(exp_add_pi_neg _).symm
   obtain ⟨n,hn⟩:=Circle.exp_eq_exp.mp hexp
   refine ⟨n,?_⟩
   dsimp [gs,T]
   rw [hn]
   field_simp
   <;> ring
 have gsconst:=continuous_integer_constant gs gsC gsZ
 obtain ⟨k,hk⟩:=gsZ 0
 have heq':(b (R p) - b (L p) - Real.pi) / T = (k:ℝ):=by
   have hh:=gsconst p
   rw [hk] at hh
   exact hh
 have heq0:(b (R 0) - b (L 0) - Real.pi) / T = (k:ℝ):=hk
 have hLpR0:L p = R 0:=by
   apply Subtype.ext
   simp [L,R,up,uzero]
 have hs0:b (L 0) = a 0:=by simpa [L,uzero] using hb0
 have hsp:b (R p) = a p:=by simpa [R,up,D] using hdiag
 have hturnk:a p - a 0 = (((2*k+1:ℤ):ℝ)) * (2*Real.pi):=by
   have heq'':=heq'
   have heq00:=heq0
   rw [hLpR0] at heq''
   rw [hsp] at heq''
   rw [hs0] at heq00
   dsimp [T] at heq'' heq00 ⊢
   have hpival:(2*Real.pi:ℝ) ≠ 0:=by positivity
   field_simp at heq'' heq00
   push_cast at heq'' heq00 ⊢
   linarith
 have hkneg:k = -1:=by
   have hpipos:0 < (2*Real.pi:ℝ):=by positivity
   have h:=hturnk
   rw [hneg] at h
   push_cast at h
   have hkr:(k:ℝ) = -1:=by nlinarith
   exact_mod_cast hkr
 have hsideval:b (L p) - a 0 = - Real.pi:=by
   have he:=heq0
   rw [hLpR0]
   rw [hs0] at he
   dsimp [T] at he
   field_simp at he
   push_cast at he
   have kk:(k:ℝ) = -1:=by exact_mod_cast hkneg
   rw [kk] at he
   linarith
 let B:ℝ → ℝ:=fun x => b (L x)
 have hBC:Continuous B:=b.continuous.comp hLc
 have hcosB:∀x ∈ Set.Icc (0:ℝ) p,0 ≤ Real.cos (B x):=by
   intro x hx
   have hleft:=switchedChord_left_re_nonneg f hf hp0 hper hmin hv0 hx.1 hx.2
   have hne:=switchedChord_ne_zero f hf hp0 hper hinj hv (L x)
   have hexp:=hb (L x)
   have hux:u x = x:=by simp [u,hx.1,hx.2]
   have hleft':0 ≤ (SC f p (L x).1) 0:=by
     simpa [L,hux] using hleft
   exact lift_cos_nonneg_of_re hne hexp hleft'
 have hB0:B 0 = a 0:=by simpa [B,L,uzero] using hb0
 have hBp:B p = a 0 - Real.pi:=by
   dsimp [B]
   linarith [hsideval]
 have hcosa0:Real.cos (a 0) = 0:=by
   have hh:=congrArg (fun v:EuclideanSpace ℝ (Fin 2) => v 0) (ha 0)
   simpa [hv0] using hh.symm
 have hs:Real.sin (a 0) = 1 ∨ Real.sin (a 0) = -1:=by
   have hu:=Real.cos_sq_add_sin_sq (a 0)
   rw [hcosa0] at hu
   have hsq:(Real.sin (a 0))^2 = 1:=by nlinarith
   exact (sq_eq_one_iff).mp hsq
 rcases hs with hs | hs
 · exact hs
 ·
   have hbad:Real.cos (a 0 - Real.pi/2) = -1:=by
     rw [Real.cos_sub,Real.cos_pi_div_two,Real.sin_pi_div_two,hcosa0,hs]
     norm_num
   have htarget:a 0 - Real.pi/2 ∈ Set.Icc (B p) (B 0):=by
     rw [hBp,hB0]
     constructor <;> linarith [Real.pi_pos]
   have hnon:(0:ℝ) ≤ p:=hp0.le
   have hex:∃t ∈ Set.Icc (0:ℝ) p,B t = a 0 - Real.pi/2:=by
     have hmem:a 0 - Real.pi/2 ∈ Set.uIcc (B 0) (B p):=by
       rw [Set.uIcc_of_ge (by rw [hBp,hB0]; linarith [Real.pi_pos])]
       exact htarget
     rcases (intermediate_value_uIcc (a:=0) (b:=p) hBC.continuousOn hmem) with ⟨t,ht,he⟩
     rw [Set.uIcc_of_le hnon] at ht
     exact ⟨t,ht,he⟩
   rcases hex with ⟨t,ht,he⟩
   have hz:=hcosB t ht
   rw [he,hbad] at hz
   linarith
def DP (u v:EuclideanSpace ℝ (Fin 2)):ℝ:=u 0 * v 1 - u 1 * v 0
lemma deriv_coord_plane (g:ℝ → EuclideanSpace ℝ (Fin 2)) (hg:ContDiff ℝ 1 g)
 (i:Fin 2) (t:ℝ):deriv (fun x:ℝ => g x i) t = (deriv g t) i:=by
 have hu:HasDerivAt g (deriv g t) t:=(hg.differentiable (by exact one_ne_zero)).differentiableAt.hasDerivAt
 let P:EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ:=EuclideanSpace.proj i
 have hpost:=P.hasFDerivAt.comp_hasDerivAt t hu
 simpa [P,Function.comp_def] using hpost.deriv
lemma area_as_xdy (g:ℝ → EuclideanSpace ℝ (Fin 2)) {p:ℝ}
 (hg:ContDiff ℝ 1 g) (hp:Function.Periodic g p) :
 (∫ t in (0:ℝ)..p,DP (g t) (deriv g t)) =
 2 * ∫ t in (0:ℝ)..p,(g t 0) * (deriv g t) 1:=by
 let X:ℝ → ℝ:=fun t => g t 0
 let Y:ℝ → ℝ:=fun t => g t 1
 have hX:ContDiff ℝ 1 X:=by
  dsimp [X]
  let P:EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ:=EuclideanSpace.proj (0:Fin 2)
  simpa [P,Function.comp_def] using (P.contDiff.comp hg)
 have hY:ContDiff ℝ 1 Y:=by
  dsimp [Y]
  let P:EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ:=EuclideanSpace.proj (1:Fin 2)
  simpa [P,Function.comp_def] using (P.contDiff.comp hg)
 have hXd:Continuous (deriv X):=hX.continuous_deriv (by norm_num)
 have hYd:Continuous (deriv Y):=hY.continuous_deriv (by norm_num)
 have hXc:Continuous X:=hX.continuous
 have hYc:Continuous Y:=hY.continuous
 have hIX:IntervalIntegrable (fun t:ℝ => deriv X t * Y t) MeasureTheory.volume 0 p :=
  (hXd.mul hYc).intervalIntegrable _ _
 have hIY:IntervalIntegrable (fun t:ℝ => X t * deriv Y t) MeasureTheory.volume 0 p :=
  (hXc.mul hYd).intervalIntegrable _ _
 have hsum :
   (∫ t in (0:ℝ)..p,deriv X t * Y t) +
     (∫ t in (0:ℝ)..p,X t * deriv Y t) = 0:=by
  have hh:=integral_deriv_contDiff_one (fun t:ℝ => X t * Y t) (hX.mul hY) 0 p
  have hpoint (t:ℝ):deriv (fun t:ℝ => X t * Y t) t = deriv X t * Y t + X t * deriv Y t:=by
    exact ((hX.differentiable (by exact one_ne_zero)).differentiableAt.hasDerivAt.mul
     (hY.differentiable (by exact one_ne_zero)).differentiableAt.hasDerivAt).deriv
  simp_rw [hpoint] at hh
  rw [intervalIntegral.integral_add hIX hIY] at hh
  have hgp:g p = g 0:=by simpa using hp 0
  have hxp:X p = X 0:=by simpa [X] using congrArg (fun z:EuclideanSpace ℝ (Fin 2) => z 0) hgp
  have hyp:Y p = Y 0:=by simpa [Y] using congrArg (fun z:EuclideanSpace ℝ (Fin 2) => z 1) hgp
  rw [hxp,hyp] at hh
  simpa using hh
 have hd0 (t:ℝ):deriv X t = deriv g t 0:=deriv_coord_plane g hg 0 t
 have hd1 (t:ℝ):deriv Y t = deriv g t 1:=deriv_coord_plane g hg 1 t
 change (∫ t in (0:ℝ)..p,g t 0 * deriv g t 1 - g t 1 * deriv g t 0) = _
 have hh :
 (∫ t in (0:ℝ)..p,X t * deriv Y t - deriv X t * Y t) =
   2 * ∫ t in (0:ℝ)..p,X t * deriv Y t:=by
  rw [intervalIntegral.integral_sub hIY hIX]
  linarith
 simpa [X,Y,hd0,hd1,mul_comm] using hh
lemma area_as_offset_xdy (g:ℝ → EuclideanSpace ℝ (Fin 2)) {p:ℝ}
 (hg:ContDiff ℝ 1 g) (hp:Function.Periodic g p) (c:ℝ) :
 (∫ t in (0:ℝ)..p,DP (g t) (deriv g t)) =
 2 * ∫ t in (0:ℝ)..p,(g t 0-c) * (deriv g t) 1:=by
 rw [area_as_xdy g hg hp]
 let Y:ℝ → ℝ:=fun t => g t 1
 have hY:ContDiff ℝ 1 Y:=by
   dsimp [Y]
   let P:EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ:=EuclideanSpace.proj (1:Fin 2)
   simpa [P,Function.comp_def] using (P.contDiff.comp hg)
 have hYd:Continuous (deriv Y):=hY.continuous_deriv (by norm_num)
 have hzero:(∫ t in (0:ℝ)..p,c * deriv g t 1) = 0:=by
   have hh:=integral_deriv_contDiff_one Y hY 0 p
   have hgp:g p = g 0:=by simpa using hp 0
   have he:Y p = Y 0:=by simpa [Y] using congrArg (fun z:EuclideanSpace ℝ (Fin 2) => z 1) hgp
   rw [he] at hh
   have hd (t:ℝ):deriv Y t = deriv g t 1:=deriv_coord_plane g hg 1 t
   have hm:(∫ t in (0:ℝ)..p,c * deriv Y t) =
       c * ∫ t in (0:ℝ)..p,deriv Y t :=
     intervalIntegral.integral_const_mul c (fun t:ℝ => deriv Y t)
   rw [hh] at hm
   norm_num at hm
   simpa [hd] using hm
 have hbaseI:IntervalIntegrable (fun t:ℝ => g t 0 * deriv g t 1)
     MeasureTheory.volume 0 p:=by
   have hxc:Continuous (fun t:ℝ => g t 0):=by fun_prop (disch:=exact hg.continuous)
   have hy:Continuous (fun t:ℝ => deriv g t 1) :=
     (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous.comp
       (hg.continuous_deriv (by norm_num))
   exact (hxc.mul hy).intervalIntegrable _ _
 have hconstI:IntervalIntegrable (fun t:ℝ => c * deriv g t 1)
     MeasureTheory.volume 0 p:=by
   have hy:Continuous (fun t:ℝ => deriv g t 1) :=
     (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous.comp
       (hg.continuous_deriv (by norm_num))
   exact (continuous_const.mul hy).intervalIntegrable _ _
 have hsplit :
     (∫ t in (0:ℝ)..p,(g t 0-c) * deriv g t 1) =
      (∫ t in (0:ℝ)..p,g t 0 * deriv g t 1) -
       (∫ t in (0:ℝ)..p,c * deriv g t 1):=by
   have he:=intervalIntegral.integral_sub hbaseI hconstI
   simpa [sub_mul] using he
 rw [hsplit,hzero]
 ring
lemma integral_shift_period {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 (F:ℝ → E) {p:ℝ} (hper: Function.Periodic F p) (s:ℝ) :
 (∫ t in (0:ℝ)..p,F (t+s)) = ∫ t in (0:ℝ)..p,F t:=by
 have he:=intervalIntegral.integral_comp_add_left F s (a:=(0:ℝ)) (b:=p)
 have he':(∫ t in (0:ℝ)..p,F (t+s)) = ∫ t in (s+0)..(s+p),F t:=by
  convert he using 1
  · congr 1; funext t; congr 1; ring
 have hp':=hper.intervalIntegral_add_eq s 0
 rw [he']
 simpa using hp'
lemma integral_detPlane_shift (g:ℝ → EuclideanSpace ℝ (Fin 2)) {p:ℝ}
 (hg:ContDiff ℝ 1 g) (hper:Function.Periodic g p) (s:ℝ) :
 (∫ t in (0:ℝ)..p,
   DP (g (t+s)) (deriv (fun x:ℝ=>g (x+s)) t)) =
 (∫ t in (0:ℝ)..p,DP (g t) (deriv g t)):=by
 let F:ℝ → ℝ:=fun t => DP (g t) (deriv g t)
 have hd:Differentiable ℝ g:=hg.differentiable (by exact one_ne_zero)
 have hdp (t:ℝ):deriv g (t+p) = deriv g t :=
  deriv_period_add g hd p hper t
 have hFp:Function.Periodic F p:=by
  intro t
  dsimp [F]
  rw [hper,hdp]
 have hsh (t:ℝ):deriv (fun x:ℝ => g (x+s)) t = deriv g (t+s) :=
  deriv_shift g hd s t
 have he:=integral_shift_period F hFp s
 simpa [F,hsh] using he
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Orientation.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Endpoint.lean
set_option linter.all false
namespace H
open Set
open scoped Topology Interval
lemma up_tangent_y_near_endpoints
   (g:ℝ → EuclideanSpace ℝ (Fin 2)) {p:ℝ}
   (hp0:0 < p) (hg:ContDiff ℝ 1 g)
   (hper:Function.Periodic g p)
   (hu:(deriv g 0) 1 = (1:ℝ)) :
   ∃δ:ℝ,0 < δ ∧ δ < p ∧
     (∀t:ℝ,0 < t → t ≤ δ → g 0 1 < g t 1) ∧
     (∀t:ℝ,p-δ ≤ t → t < p → g t 1 < g 0 1):=by
 let Y:ℝ → ℝ:=fun t => g t 1
 have hY:ContDiff ℝ 1 Y:=by
   dsimp [Y]
   let P:EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ:=EuclideanSpace.proj (1:Fin 2)
   simpa [P,Function.comp_def] using (P.contDiff.comp hg)
 have hYc:Continuous Y:=hY.continuous
 have hYd:Continuous (deriv Y):=hY.continuous_deriv (by norm_num)
 have hd0:deriv Y 0 = 1:=by
   simpa [Y,H.deriv_coord_plane g hg 1 0] using hu
 have hopen:IsOpen {t:ℝ | 0 < deriv Y t} :=
   isOpen_lt continuous_const hYd
 have hmem:(0:ℝ) ∈ {t:ℝ | 0 < deriv Y t}:=by
   change 0 < deriv Y 0
   rw [hd0]
   norm_num
 have hnh:{t:ℝ | 0 < deriv Y t} ∈ 𝓝 (0:ℝ):=hopen.mem_nhds hmem
 rcases Metric.mem_nhds_iff.1 hnh with ⟨e,he,heall⟩
 let δ:ℝ:=min (p/2) (e/2)
 have hδ0:0 < δ:=by
   dsimp [δ]
   exact lt_min (by linarith) (by linarith)
 have hδp:δ < p:=lt_of_le_of_lt (min_le_left _ _) (by linarith)
 have hδe:δ < e:=lt_of_le_of_lt (min_le_right _ _) (by linarith)
 have hpos0 {x:ℝ} (hx0:0 ≤ x) (hxδ:x ≤ δ):0 < deriv Y x:=by
   have hxball:x ∈ Metric.ball (0:ℝ) e:=by
     rw [mem_ball_zero_iff,Real.norm_eq_abs]
     have:|x| = x:=abs_of_nonneg hx0
     rw [this]
     exact lt_of_le_of_lt hxδ hδe
   exact heall hxball
 have hYper:Function.Periodic Y p:=by
   intro t
   dsimp [Y]
   simpa using congrArg (fun z:EuclideanSpace ℝ (Fin 2) => z 1) (hper t)
 have hYdiff:Differentiable ℝ Y :=
   hY.differentiable (by exact one_ne_zero)
 have hposp {x:ℝ} (hlo:p-δ ≤ x) (hhi:x ≤ p):0 < deriv Y x:=by
   have hx0:-δ ≤ x-p:=by linarith
   have hx1:x-p ≤ 0:=by linarith
   have hxball:(x-p) ∈ Metric.ball (0:ℝ) e:=by
     rw [mem_ball_zero_iff,Real.norm_eq_abs]
     rw [abs_of_nonpos hx1]
     have:-(x-p) ≤ δ:=by linarith
     exact lt_of_le_of_lt this hδe
   have hxnear:0 < deriv Y (x-p):=heall hxball
   have hrep:=H.deriv_period_add Y hYdiff p hYper (x-p)
   have heq:x-p+p = x:=by ring
   rw [heq] at hrep
   rw [hrep]
   exact hxnear
 have hmono0:StrictMonoOn Y (Set.Icc (0:ℝ) δ):=by
   apply strictMonoOn_of_deriv_pos (convex_Icc (0:ℝ) δ) hYc.continuousOn
   intro x hx
   rw [interior_Icc] at hx
   exact hpos0 hx.1.le hx.2.le
 have hmonop:StrictMonoOn Y (Set.Icc (p-δ) p):=by
   apply strictMonoOn_of_deriv_pos (convex_Icc (p-δ) p) hYc.continuousOn
   intro x hx
   rw [interior_Icc] at hx
   exact hposp hx.1.le hx.2.le
 have hYp:Y p = Y 0:=by
   simpa using hYper 0
 refine ⟨δ,hδ0,hδp,?_,?_⟩
 · intro t ht htδ
   have hz:(0:ℝ) ∈ Set.Icc (0:ℝ) δ:=⟨le_rfl,hδ0.le⟩
   have htmem:t ∈ Set.Icc (0:ℝ) δ:=⟨ht.le,htδ⟩
   have hlt:=hmono0 hz htmem ht
   exact hlt
 · intro t htlow htlt
   have htmem:t ∈ Set.Icc (p-δ) p:=⟨htlow,htlt.le⟩
   have hpmem:p ∈ Set.Icc (p-δ) p:=⟨by linarith,le_rfl⟩
   have hlt:=hmonop htmem hpmem htlt
   change Y t < Y 0
   rw [← hYp]
   exact hlt
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Endpoint.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Polygon.lean
set_option linter.all false
namespace H
open Set
variable {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma cyclic_ordered_edges_ne
   (f:ℝ → F) {p d ρ Δ:ℝ}
   (hp:0 < p) (hd:0 < d) (hdp:d < p/2)
   (hΔ:0 < Δ) (hsmall:Δ < d/2) (hshort:2*Δ < ρ)
   (hper:Function.Periodic f p)
   (hnear:∀{u a b c e:ℝ},
     u ∈ Set.Icc (-p) (2*p) → a ∈ Set.Icc (-p) (2*p) → b ∈ Set.Icc (-p) (2*p) → c ∈ Set.Icc (-p) (2*p) → e ∈ Set.Icc (-p) (2*p) → |a-u| < d → |b-u| < d → |c-u| < d → |e-u| < d → a < b → b ≤ c → c < e → ∀l m:ℝ,0 ≤ l → l < 1 → 0 ≤ m → m ≤ 1 → f a + l • (f b - f a) ≠ f c + m • (f e - f c))
   (hfar:∀{a b c e l m L:ℝ},
     a ∈ Set.Icc (0:ℝ) p → c ∈ Set.Icc (0:ℝ) p → d/2 ≤ |c-a| → |c-a| ≤ p-d/2 → a ≤ b → c ≤ e → b-a ≤ L → e-c ≤ L → 2*L < ρ → 0 ≤ l → l ≤ 1 → 0 ≤ m → m ≤ 1 → f a + l • (f b - f a) ≠ f c + m • (f e - f c))
   {a c l m:ℝ}
   (ha0:0 ≤ a) (hord:a + Δ ≤ c) (hcend:c + Δ ≤ p)
   (hl0:0 ≤ l) (hl1:l < 1) (hm0:0 ≤ m) (hm1:m < 1) :
   f a + l • (f (a+Δ) - f a) ≠
     f c + m • (f (c+Δ) - f c):=by
 have hac:a ≤ c:=by linarith
 have hc0:0 ≤ c:=le_trans ha0 hac
 have hap:a ≤ p:=by linarith
 have hcp:c ≤ p:=by linarith
 have hae:a + Δ ≤ p:=le_trans hord (by linarith)
 have hab0:0 ≤ a+Δ:=by linarith
 have hce0:0 ≤ c+Δ:=by linarith
 have hd':0 < d/2:=by linarith
 by_cases hleft:c-a < d/2
 ·
   have hu:a ∈ Set.Icc (-p) (2*p):=by constructor <;> linarith
   have hb:a+Δ ∈ Set.Icc (-p) (2*p):=by constructor <;> linarith
   have hcI:c ∈ Set.Icc (-p) (2*p):=by constructor <;> linarith
   have he:c+Δ ∈ Set.Icc (-p) (2*p):=by constructor <;> linarith
   apply hnear (u:=a) hu hu hb hcI he (by simp [hd])
     (by rw [show a+Δ-a=Δ by ring,abs_of_pos hΔ]; linarith)
     (by rw [abs_of_nonneg (sub_nonneg.mpr hac)]; linarith)
     (by rw [abs_of_nonneg (by linarith:0 ≤ c+Δ-a)]; linarith)
     (by linarith) (by linarith) (by linarith) l m hl0 hl1 hm0 (le_of_lt hm1)
 · have hlow:d/2 ≤ |c-a|:=by
     rw [abs_of_nonneg (sub_nonneg.mpr hac)]
     linarith
   by_cases hmid:c-a ≤ p-d/2
   · apply hfar (a:=a) (b:=a+Δ) (c:=c) (e:=c+Δ) (L:=Δ)
         ⟨ha0,hap⟩ ⟨hc0,hcp⟩ hlow
     · simpa [abs_of_nonneg (sub_nonneg.mpr hac)] using hmid
     · linarith
     · linarith
     · linarith
     · linarith
     · simpa using hshort
     · exact hl0
     · exact le_of_lt hl1
     · exact hm0
     · exact le_of_lt hm1
   ·
     have hlarge:p-d/2 < c-a:=lt_of_not_ge hmid
     have alow:a < d/2 - Δ:=by linarith
     have clow:p-d/2 < c:=by linarith
     have hpu:p ∈ Set.Icc (-p) (2*p):=by constructor <;> linarith
     have hci:c ∈ Set.Icc (-p) (2*p):=by constructor <;> linarith
     have hcei:c+Δ ∈ Set.Icc (-p) (2*p):=by constructor <;> linarith
     have hai:a+p ∈ Set.Icc (-p) (2*p):=by constructor <;> linarith
     have habi:a+Δ+p ∈ Set.Icc (-p) (2*p):=by constructor <;> linarith
     have hna:|c-p| < d:=by
       rw [abs_of_nonpos (by linarith:c-p ≤ 0)]
       linarith
     have hnb:|c+Δ-p| < d:=by
       rw [abs_of_nonpos (by linarith:c+Δ-p ≤ 0)]
       linarith
     have hnc:|a+p-p| < d:=by
       rw [show a+p-p=a by ring,abs_of_nonneg ha0]
       linarith
     have hne:|a+Δ+p-p| < d:=by
       rw [show a+Δ+p-p=a+Δ by ring,abs_of_nonneg hab0]
       linarith
     have hdis:=hnear (u:=p) hpu hci hcei hai habi hna hnb hnc hne
         (by linarith:c < c+Δ)
         (by linarith:c+Δ ≤ a+p)
         (by linarith:a+p < a+Δ+p)
         m l hm0 hm1 hl0 (le_of_lt hl1)
     intro hEq
     apply hdis
     have hp1:f (a+p) = f a:=hper a
     have hp2:f (a+Δ+p) = f (a+Δ):=by
       convert hper (a+Δ) using 2 <;> ring
     simpa [hp1,hp2] using hEq.symm
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Polygon.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/AreaApprox.lean
set_option linter.all false
namespace H
open Set
open scoped Interval Topology
lemma xdy_edge_left_error
   (X Y:ℝ → ℝ) (hX:ContDiff ℝ 1 X) (hY:ContDiff ℝ 1 Y)
   (bndX:∀t:ℝ,|deriv X t| ≤ (1:ℝ))
   (bndY:∀t:ℝ,|deriv Y t| ≤ (1:ℝ))
   {a b:ℝ} (hab:a ≤ b) :
   |(∫ t in a..b,X t * deriv Y t) - X a * (Y b - Y a)| ≤ (b-a)^2:=by
 have hXdiff:∀x:ℝ,DifferentiableAt ℝ X x :=
   fun x => (hX.differentiable (by exact one_ne_zero)).differentiableAt
 have hYdiff:∀x:ℝ,DifferentiableAt ℝ Y x :=
   fun x => (hY.differentiable (by exact one_ne_zero)).differentiableAt
 have hYd:Continuous (deriv Y):=hY.continuous_deriv (by norm_num)
 have hXc:Continuous X:=hX.continuous
 have hmainI:IntervalIntegrable (fun t:ℝ => X t * deriv Y t)
     MeasureTheory.volume a b :=
   (hXc.mul hYd).intervalIntegrable _ _
 have hconstI:IntervalIntegrable (fun t:ℝ => X a * deriv Y t)
     MeasureTheory.volume a b :=
   (continuous_const.mul hYd).intervalIntegrable _ _
 have hYftc:(∫ t in a..b,deriv Y t) = Y b - Y a :=
   integral_deriv_contDiff_one Y hY a b
 have hrewrite :
     (∫ t in a..b,(X t-X a) * deriv Y t) =
       (∫ t in a..b,X t * deriv Y t) - X a * (Y b - Y a):=by
   have hh:=intervalIntegral.integral_sub hmainI hconstI
   have hc:=intervalIntegral.integral_const_mul (μ:=MeasureTheory.volume)
      (a:=a) (b:=b) (X a) (fun t:ℝ => deriv Y t)
   rw [hYftc] at hc
   calc
     (∫ t in a..b,(X t-X a) * deriv Y t) =
         (∫ t in a..b,X t * deriv Y t) -
           (∫ t in a..b,X a * deriv Y t):=by
             simpa [sub_mul] using hh
     _ = _:=by rw [hc]
 rw [← hrewrite]
 have hpoint:∀t ∈ Set.Icc a b,
     |(X t-X a) * deriv Y t| ≤ (b-a):=by
   intro t ht
   have hx:=Convex.norm_image_sub_le_of_norm_deriv_le
     (𝕜:=ℝ) (G:=ℝ) (f:=X) (C:=(1:ℝ)) (s:=Set.univ)
     (by intro z hz; exact hXdiff z)
     (by intro z hz; simpa [Real.norm_eq_abs] using bndX z)
     (convex_univ) (show a ∈ (Set.univ:Set ℝ) by trivial)
     (show t ∈ (Set.univ:Set ℝ) by trivial)
   have hxt:|X t-X a| ≤ t-a:=by
     simpa [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht.1)] using hx
   have hy:=bndY t
   have hn0:0 ≤ |X t-X a|:=abs_nonneg _
   calc
     |(X t-X a) * deriv Y t|
         = |X t-X a| * |deriv Y t|:=abs_mul _ _
     _ ≤ |X t-X a| * 1:=mul_le_mul_of_nonneg_left hy hn0
     _ ≤ (b-a):=by
       have:|X t-X a| ≤ b-a:=le_trans hxt (by linarith [ht.2])
       simpa using this
 have hbound:=intervalIntegral.norm_integral_le_of_norm_le_const
   (f:=fun t:ℝ => (X t-X a) * deriv Y t) (C:=b-a)
   (a:=a) (b:=b) (by
     intro t ht
     rw [uIoc_of_le hab] at ht
     simpa [Real.norm_eq_abs] using hpoint t ⟨ht.1.le,ht.2⟩)
 have hnon:0 ≤ b-a:=sub_nonneg.mpr hab
 simpa [Real.norm_eq_abs,abs_of_nonneg hnon,pow_two] using hbound
end H
namespace H
open Set
open scoped Interval Topology BigOperators
lemma xdy_mesh_left_error
   (X Y:ℝ → ℝ) (hX:ContDiff ℝ 1 X) (hY:ContDiff ℝ 1 Y)
   (bndX:∀t:ℝ,|deriv X t| ≤ (1:ℝ))
   (bndY:∀t:ℝ,|deriv Y t| ≤ (1:ℝ))
   (Δ:ℝ) (hΔ:0 ≤ Δ) (n:ℕ) :
   |(∫ t in (0:ℝ)..(n:ℝ)*Δ,X t * deriv Y t) -
       ∑ i ∈ Finset.range n,
         X ((i:ℝ)*Δ) * (Y (((i+1:ℕ):ℝ)*Δ) - Y ((i:ℝ)*Δ))|
     ≤ (n:ℝ) * Δ^2:=by
 have hYd:Continuous (deriv Y):=hY.continuous_deriv (by norm_num)
 have hXc:Continuous X:=hX.continuous
 have hInt (a b:ℝ):IntervalIntegrable (fun t:ℝ => X t * deriv Y t)
     MeasureTheory.volume a b:=(hXc.mul hYd).intervalIntegrable _ _
 induction n with
 | zero => simp
 | succ n ih =>
     let t:ℝ:=(n:ℝ)*Δ
     let u:ℝ:=((n+1:ℕ):ℝ)*Δ
     have htu:t ≤ u:=by
       dsimp [t,u]
       push_cast
       nlinarith
     have hedge:=xdy_edge_left_error X Y hX hY bndX bndY htu
     have hadd:=intervalIntegral.integral_add_adjacent_intervals
       (hInt 0 t) (hInt t u)
     have huform:((n+1:ℕ):ℝ)*Δ = u:=rfl
     have htform:(n:ℝ)*Δ = t:=rfl
     have hsum :
         (∑ i ∈ Finset.range (Nat.succ n),
           X ((i:ℝ)*Δ) * (Y (((i+1:ℕ):ℝ)*Δ) - Y ((i:ℝ)*Δ))) =
           (∑ i ∈ Finset.range n,
           X ((i:ℝ)*Δ) * (Y (((i+1:ℕ):ℝ)*Δ) - Y ((i:ℝ)*Δ))) +
             X t * (Y u - Y t):=by
       rw [Finset.sum_range_succ]
     rw [hsum]
     change |(∫ z in (0:ℝ)..u,X z * deriv Y z) -
       ((∑ i ∈ Finset.range n,
         X ((i:ℝ)*Δ) * (Y (((i+1:ℕ):ℝ)*Δ) - Y ((i:ℝ)*Δ))) +
           X t * (Y u - Y t))| ≤ ((n+1:ℕ):ℝ) * Δ^2
     rw [← hadd]
     have htri :
       |((∫ z in (0:ℝ)..t,X z * deriv Y z) -
           (∑ i ∈ Finset.range n,
             X ((i:ℝ)*Δ) * (Y (((i+1:ℕ):ℝ)*Δ) - Y ((i:ℝ)*Δ)))) +
         ((∫ z in t..u,X z * deriv Y z) - X t * (Y u - Y t))|
         ≤
       |(∫ z in (0:ℝ)..t,X z * deriv Y z) -
           (∑ i ∈ Finset.range n,
             X ((i:ℝ)*Δ) * (Y (((i+1:ℕ):ℝ)*Δ) - Y ((i:ℝ)*Δ)))| +
       |(∫ z in t..u,X z * deriv Y z) - X t * (Y u - Y t)| :=
         abs_add_le _ _
     have htlen:u-t = Δ:=by
       dsimp [u,t]
       push_cast
       ring
     have hedge' :
         |(∫ z in t..u,X z * deriv Y z) - X t * (Y u - Y t)| ≤ Δ^2:=by
       simpa [htlen] using hedge
     have ih' :
         |(∫ z in (0:ℝ)..t,X z * deriv Y z) -
           (∑ i ∈ Finset.range n,
             X ((i:ℝ)*Δ) * (Y (((i+1:ℕ):ℝ)*Δ) - Y ((i:ℝ)*Δ)))|
             ≤ (n:ℝ) * Δ^2:=by
         simpa [t] using ih
     calc
       |((∫ z in (0:ℝ)..t,X z * deriv Y z) + (∫ z in t..u,X z * deriv Y z)) -
         ((∑ i ∈ Finset.range n,
           X ((i:ℝ)*Δ) * (Y (((i+1:ℕ):ℝ)*Δ) - Y ((i:ℝ)*Δ))) +
             X t * (Y u - Y t))|
         = |((∫ z in (0:ℝ)..t,X z * deriv Y z) -
               (∑ i ∈ Finset.range n,
                 X ((i:ℝ)*Δ) * (Y (((i+1:ℕ):ℝ)*Δ) - Y ((i:ℝ)*Δ)))) +
             ((∫ z in t..u,X z * deriv Y z) - X t * (Y u - Y t))|:=by congr 1 <;> ring
       _ ≤ |(∫ z in (0:ℝ)..t,X z * deriv Y z) -
               (∑ i ∈ Finset.range n,
                 X ((i:ℝ)*Δ) * (Y (((i+1:ℕ):ℝ)*Δ) - Y ((i:ℝ)*Δ)))| +
             |(∫ z in t..u,X z * deriv Y z) - X t * (Y u - Y t)|:=htri
       _ ≤ (n:ℝ) * Δ^2 + Δ^2:=add_le_add ih' hedge'
       _ = ((n+1:ℕ):ℝ) * Δ^2:=by push_cast; ring
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/AreaApprox.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/MeshReduction.lean
set_option linter.all false
namespace H
open Set
open scoped Interval Topology BigOperators
abbrev MRPlane:=EuclideanSpace ℝ (Fin 2)
lemma coord_contDiff_one (g:ℝ → MRPlane) (hg:ContDiff ℝ 1 g) (i:Fin 2) :
   ContDiff ℝ 1 (fun t:ℝ => g t i):=by
 let P:MRPlane →L[ℝ] ℝ:=EuclideanSpace.proj i
 simpa [P,Function.comp_def] using (P.contDiff.comp hg)
lemma coord_deriv_abs_le_one (g:ℝ → MRPlane) (hg:ContDiff ℝ 1 g)
   (hv:∀t:ℝ,‖deriv g t‖ = (1:ℝ)) (i:Fin 2) (t:ℝ) :
   |deriv (fun x:ℝ => g x i) t| ≤ (1:ℝ):=by
 rw [deriv_coord_plane g hg i t]
 have hcoord:‖(deriv g t) i‖ ≤ ‖deriv g t‖ :=
   PiLp.norm_apply_le (deriv g t) i
 simpa [Real.norm_eq_abs,hv t] using hcoord
lemma curve_xdy_mesh_error (g:ℝ → MRPlane) (hg:ContDiff ℝ 1 g)
   (hv:∀t:ℝ,‖deriv g t‖ = (1:ℝ))
   (c Δ:ℝ) (hΔ:0 ≤ Δ) (n:ℕ) :
   |(∫ t in (0:ℝ)..(n:ℝ)*Δ,
         (g t 0 - c) * (deriv g t) 1) -
       ∑ i ∈ Finset.range n,
         (g ((i:ℝ)*Δ) 0 - c) *
           (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)|
     ≤ (n:ℝ) * Δ^2:=by
 let X:ℝ → ℝ:=fun t => g t 0 - c
 let Y:ℝ → ℝ:=fun t => g t 1
 have hX:ContDiff ℝ 1 X :=
   (coord_contDiff_one g hg 0).sub contDiff_const
 have hY:ContDiff ℝ 1 Y:=coord_contDiff_one g hg 1
 have hdsub (t:ℝ):deriv X t = deriv (fun u:ℝ => g u 0) t:=by
   dsimp [X]
   have h1:DifferentiableAt ℝ (fun u:ℝ => g u 0) t :=
     ((coord_contDiff_one g hg 0).differentiable (by exact one_ne_zero)).differentiableAt
   simpa using (h1.hasDerivAt.sub_const c).deriv
 have hdx (t:ℝ):|deriv X t| ≤ (1:ℝ):=by
   rw [hdsub]
   exact coord_deriv_abs_le_one g hg hv 0 t
 have hdy (t:ℝ):|deriv Y t| ≤ (1:ℝ) :=
   coord_deriv_abs_le_one g hg hv 1 t
 have hh:=xdy_mesh_left_error X Y hX hY hdx hdy Δ hΔ n
 simpa [X,Y,deriv_coord_plane g hg] using hh
lemma exists_simple_step_window (g:ℝ → MRPlane) {p:ℝ} (hp:0 < p)
   (hg:ContDiff ℝ 1 g) (hper:Function.Periodic g p)
   (hinj:Set.InjOn g (Set.Ico (0:ℝ) p))
   (hv:∀x:ℝ,‖deriv g x‖ = (1:ℝ)) :
   ∃η:ℝ,0 < η ∧
     ∀{Δ a c l m:ℝ},
       0 < Δ → Δ < η → 0 ≤ a → a + Δ ≤ c → c + Δ ≤ p → 0 ≤ l → l < 1 → 0 ≤ m → m < 1 → g a + l • (g (a+Δ) - g a) ≠
        g c + m • (g (c+Δ) - g c):=by
 obtain ⟨d,hd,hdhalf,hwin⟩ :=
   exists_period_cone_window (F:=MRPlane) g hp hg hper hv
 have hd2:0 < d/2:=by linarith
 have h2d:2*(d/2) ≤ p:=by linarith
 obtain ⟨ρ,hρ,hgap⟩ :=
   exists_pos_forall_norm_sub_of_separated
     g hg.continuous hp hd2 h2d hper hinj
 have hfar {a b c e l m L:ℝ}
       (haI:a ∈ Set.Icc (0:ℝ) p)
       (hcI:c ∈ Set.Icc (0:ℝ) p)
       (hsep:d/2 ≤ |c-a|) (hsep':|c-a| ≤ p-d/2)
       (hab:a ≤ b) (hce:c ≤ e)
       (hb:b-a ≤ L) (he:e-c ≤ L) (hL:2*L < ρ)
       (hl0:0 ≤ l) (hl1:l ≤ 1) (hm0:0 ≤ m) (hm1:m ≤ 1) :
       g a + l • (g b - g a) ≠ g c + m • (g e - g c):=by
     exact affine_edges_ne_of_parameter_gap g hg hv hgap haI hcI hsep hsep'
         hab hce hb he hL hl0 hl1 hm0 hm1
 have hnear
       {u a b c e l m:ℝ}
       (hu:u ∈ Set.Icc (-p) (2*p))
       (ha0:a ∈ Set.Icc (-p) (2*p))
       (hb0:b ∈ Set.Icc (-p) (2*p))
       (hc0:c ∈ Set.Icc (-p) (2*p))
       (he0:e ∈ Set.Icc (-p) (2*p))
       (hau:|a-u| < d) (hbu:|b-u| < d)
       (hcu:|c-u| < d) (heu:|e-u| < d)
       (hab:a < b) (hbc:b ≤ c) (hce:c < e)
       (hl0:0 ≤ l) (hl1:l < 1) (hm0:0 ≤ m) (hm1:m ≤ 1) :
       g a + l • (g b - g a) ≠ g c + m • (g e - g c):=by
     have hvone:=(hwin u hu u hu (by simpa using hd)).1
     have hae0:a ≤ e:=by linarith
     have ha':a ∈ Set.Icc a e:=⟨le_rfl,hae0⟩
     have hb':b ∈ Set.Icc a e:=⟨by linarith,by linarith⟩
     have hc':c ∈ Set.Icc a e:=⟨by linarith,by linarith⟩
     have he':e ∈ Set.Icc a e:=⟨hae0,le_rfl⟩
     apply affine_edges_ne_of_deriv_close g hg
       (deriv g u) hvone ha' hb' hc' he' hab hbc hce hl0 hl1 hm0 hm1
     intro x hx
     have hxu:|x-u| < d:=by
       have hxa:a ≤ x:=hx.1
       have hxe:x ≤ e:=hx.2
       have hlo:u-d < a:=by
         have hh:=(abs_lt.mp hau).1; linarith
       have hhi:e < u+d:=by
         have hh:=(abs_lt.mp heu).2; linarith
       rw [abs_lt]
       constructor <;> linarith
     have hxlarge:x ∈ Set.Icc (-p) (2*p):=by
       exact ⟨le_trans ha0.1 hx.1,le_trans hx.2 he0.2⟩
     exact (hwin u hu x hxlarge hxu).2
 refine ⟨min (d/2) (ρ/2),lt_min hd2 (by linarith),?_⟩
 intro Δ a c l m hΔ hΔsmall ha0 hord hend hl0 hl1 hm0 hm1
 have hΔd:Δ < d/2:=lt_of_lt_of_le hΔsmall (min_le_left _ _)
 have hΔρ:2*Δ < ρ:=by
   have hlt:Δ < ρ/2:=lt_of_lt_of_le hΔsmall (min_le_right _ _)
   linarith
 apply cyclic_ordered_edges_ne g hp hd hdhalf hΔ hΔd hΔρ hper (ρ:=ρ)
 · intro u a' b' c' e' hu ha hb hc he hau hbu hcu heu hab hbc hce
   intro l' m' l0 l1 m0 m1
   exact hnear hu ha hb hc he hau hbu hcu heu hab hbc hce l0 l1 m0 m1
 · intro a' b' c' e' l' m' L ha hc hsep hsep' hab hce hb he hL l0 l1 m0 m1
   exact hfar ha hc hsep hsep' hab hce hb he hL l0 l1 m0 m1
 · exact ha0
 · exact hord
 · exact hend
 · exact hl0
 · exact hl1
 · exact hm0
 · exact hm1
lemma exists_simple_mesh_below (g:ℝ → MRPlane) {p η ε:ℝ}
   (hp:0 < p) (hη:0 < η) (hε:0 < ε)
   (hstep:∀{Δ a c l m:ℝ},
       0 < Δ → Δ < η → 0 ≤ a → a + Δ ≤ c → c + Δ ≤ p → 0 ≤ l → l < 1 → 0 ≤ m → m < 1 → g a + l • (g (a+Δ) - g a) ≠
         g c + m • (g (c+Δ) - g c)) :
  ∃n:ℕ,0 < n ∧
    let Δ:ℝ:=p / (n:ℝ)
    0 < Δ ∧ Δ < η ∧ Δ < ε ∧
      ∀i j:ℕ,i < j → j < n → ∀l m:ℝ,0 ≤ l → l < 1 → 0 ≤ m → m < 1 → g ((i:ℝ)*Δ) + l • (g (((i+1:ℕ):ℝ)*Δ) - g ((i:ℝ)*Δ)) ≠
          g ((j:ℝ)*Δ) + m • (g (((j+1:ℕ):ℝ)*Δ) - g ((j:ℝ)*Δ)):=by
 let q:ℝ:=min η ε
 have hq:0 < q:=lt_min hη hε
 obtain ⟨n,hn⟩:=exists_nat_gt (p / q)
 have hn0r:(0:ℝ) < n:=lt_of_le_of_lt
    (by positivity:(0:ℝ) ≤ p / q) hn
 have hn0:0 < n:=by exact_mod_cast hn0r
 let Δ:ℝ:=p / (n:ℝ)
 have hpos:0 < Δ:=by dsimp [Δ]; positivity
 have hlt:Δ < q:=by
   dsimp [Δ] at *
   apply (div_lt_iff₀ hn0r).2
   have hh:=(div_lt_iff₀ hq).1 hn
   nlinarith
 have hη':Δ < η:=lt_of_lt_of_le hlt (min_le_left _ _)
 have hε':Δ < ε:=lt_of_lt_of_le hlt (min_le_right _ _)
 refine ⟨n,hn0,?_⟩
 dsimp
 refine ⟨hpos,hη',hε',?_⟩
 intro i j hij hjn l m hl0 hl1 hm0 hm1
 have hacNat:i+1 ≤ j:=(Nat.add_one_le_iff).2 hij
 have hceNat:j+1 ≤ n:=hjn
 have hacR:(i:ℝ) + 1 ≤ (j:ℝ):=by exact_mod_cast hacNat
 have hceR:(j:ℝ) + 1 ≤ (n:ℝ):=by exact_mod_cast hceNat
 have ha0:0 ≤ (i:ℝ)*Δ:=mul_nonneg (by positivity) hpos.le
 have hord:(i:ℝ)*Δ + Δ ≤ (j:ℝ)*Δ:=by nlinarith
 have hend:(j:ℝ)*Δ + Δ ≤ p:=by
   have hpiden:(n:ℝ)*Δ = p:=by dsimp [Δ]; field_simp
   rw [← hpiden]
   nlinarith
 have hh:=hstep hpos hη' ha0 hord hend hl0 hl1 hm0 hm1
 simpa [Nat.cast_add,Nat.cast_one,add_mul] using hh
end H
namespace H
open scoped BigOperators
lemma coord_sub_abs_le_length (g:ℝ → MRPlane) (hg:ContDiff ℝ 1 g)
   (hv:∀t:ℝ,‖deriv g t‖ = (1:ℝ)) (i:Fin 2)
   {a b:ℝ} (hab:a ≤ b) :
   |g b i - g a i| ≤ b-a:=by
 let X:ℝ → ℝ:=fun t => g t i
 have hXd:∀x:ℝ,DifferentiableAt ℝ X x :=
   fun x => ((coord_contDiff_one g hg i).differentiable
     (by exact one_ne_zero)).differentiableAt
 have hbnd:∀z:ℝ,‖deriv X z‖ ≤ (1:ℝ):=by
   intro z
   simpa [Real.norm_eq_abs,X] using coord_deriv_abs_le_one g hg hv i z
 have hh:=Convex.norm_image_sub_le_of_norm_deriv_le
     (𝕜:=ℝ) (G:=ℝ) (f:=X) (C:=(1:ℝ)) (s:=Set.univ)
     (by intro z hz; exact hXd z)
     (by intro z hz; exact hbnd z)
     (convex_univ)
     (show a ∈ (Set.univ:Set ℝ) by trivial)
     (show b ∈ (Set.univ:Set ℝ) by trivial)
 simpa [X,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] using hh
lemma curve_trapezoid_sub_left_le (g:ℝ → MRPlane)
   (hg:ContDiff ℝ 1 g) (hv:∀t:ℝ,‖deriv g t‖ = (1:ℝ))
   (c Δ:ℝ) (hΔ:0 ≤ Δ) (n:ℕ) :
   |(∑ i ∈ Finset.range n,
         (((g ((i:ℝ)*Δ) 0 - c) +
            (g (((i+1:ℕ):ℝ)*Δ) 0 - c)) / 2) *
            (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)) -
      (∑ i ∈ Finset.range n,
         (g ((i:ℝ)*Δ) 0 - c) *
            (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1))|
     ≤ (n:ℝ) * Δ^2 / 2:=by
 have hedgelen (i:ℕ) (k:Fin 2) :
     |g (((i+1:ℕ):ℝ)*Δ) k - g ((i:ℝ)*Δ) k| ≤ Δ:=by
   have hord:(i:ℝ)*Δ ≤ ((i+1:ℕ):ℝ)*Δ:=by
     push_cast
     nlinarith
   have hh:=coord_sub_abs_le_length g hg hv k hord
   convert hh using 1 <;> push_cast
   ring
 let Q:ℕ → ℝ:=fun i =>
      (((g ((i:ℝ)*Δ) 0 - c) +
            (g (((i+1:ℕ):ℝ)*Δ) 0 - c)) / 2) *
            (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)
 let L:ℕ → ℝ:=fun i =>
         (g ((i:ℝ)*Δ) 0 - c) *
            (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)
 have hpoint (i:ℕ):|Q i - L i| ≤ Δ^2/2:=by
   have hx:=hedgelen i (0:Fin 2)
   have hy:=hedgelen i (1:Fin 2)
   have hp:0 ≤ Δ:=hΔ
   have hxnon:0 ≤ |g (((i+1:ℕ):ℝ)*Δ) 0 - g ((i:ℝ)*Δ) 0|:=abs_nonneg _
   have hm:|(g (((i+1:ℕ):ℝ)*Δ) 0 - g ((i:ℝ)*Δ) 0) *
                 (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)| ≤ Δ^2:=by
     rw [abs_mul]
     have hn:=abs_nonneg (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)
     calc
       |g (((i+1:ℕ):ℝ)*Δ) 0 - g ((i:ℝ)*Δ) 0| *
         |g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1| ≤ Δ * Δ :=
           mul_le_mul hx hy hn hp
       _ = Δ^2:=by ring
   have heq:Q i - L i =
         ((g (((i+1:ℕ):ℝ)*Δ) 0 - g ((i:ℝ)*Δ) 0) *
            (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)) / 2:=by
     dsimp [Q,L]
     ring
   rw [heq]
   calc
     |((g (((i+1:ℕ):ℝ)*Δ) 0 - g ((i:ℝ)*Δ) 0) *
            (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)) / 2|
         = |((g (((i+1:ℕ):ℝ)*Δ) 0 - g ((i:ℝ)*Δ) 0) *
            (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1))| / 2:=by
               rw [abs_div]
               norm_num
     _ ≤ Δ^2/2:=by linarith
 rw [← Finset.sum_sub_distrib]
 calc
   |∑ i ∈ Finset.range n,(Q i - L i)|
      ≤ ∑ i ∈ Finset.range n,|Q i - L i| :=
         Finset.abs_sum_le_sum_abs _ _
   _ ≤ ∑ _i ∈ Finset.range n,(Δ^2/2):=by
         exact Finset.sum_le_sum (by
           intro i hi; exact hpoint i)
   _ = (n:ℝ) * Δ^2 / 2:=by
         simp
         ring
end H
namespace H
open Set
open scoped Interval Topology BigOperators
lemma exists_positive_simple_support_mesh
   (g:ℝ → MRPlane) {p δ:ℝ} (hp:0 < p)
   (hg:ContDiff ℝ 1 g) (hper:Function.Periodic g p)
   (hinj:Set.InjOn g (Set.Ico (0:ℝ) p))
   (hv:∀t:ℝ,‖deriv g t‖ = (1:ℝ))
   (hmin:∀t ∈ Set.Icc (0:ℝ) p,g 0 0 ≤ g t 0)
   (hδ0:0 < δ) (hδp:δ < p)
   (hup:∀{t:ℝ},0 < t → t ≤ δ → g 0 1 < g t 1)
   (hdown:∀{t:ℝ},p-δ ≤ t → t < p → g t 1 < g 0 1)
   (hpos:0 < ∫ t in (0:ℝ)..p,(g t 0 - g 0 0) * (deriv g t) 1) :
  ∃n:ℕ,0 < n ∧
    let Δ:ℝ:=p / (n:ℝ)
    0 < Δ ∧ Δ < δ ∧
      g 0 1 < g Δ 1 ∧ g (p-Δ) 1 < g 0 1 ∧
      (∀i:ℕ,i < n → 0 ≤ g ((i:ℝ)*Δ) 0 - g 0 0) ∧
      (∀i j:ℕ,i < j → j < n → ∀l m:ℝ,0 ≤ l → l < 1 → 0 ≤ m → m < 1 → g ((i:ℝ)*Δ) + l • (g (((i+1:ℕ):ℝ)*Δ) - g ((i:ℝ)*Δ)) ≠
          g ((j:ℝ)*Δ) + m • (g (((j+1:ℕ):ℝ)*Δ) - g ((j:ℝ)*Δ))) ∧
      (0 < ∑ i ∈ Finset.range n,
         (g ((i:ℝ)*Δ) 0 - g 0 0) *
           (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)) ∧
      (0 < ∑ i ∈ Finset.range n,
         (((g ((i:ℝ)*Δ) 0 - g 0 0) +
            (g (((i+1:ℕ):ℝ)*Δ) 0 - g 0 0)) / 2) *
            (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)):=by
 obtain ⟨η,hη,hstep⟩ :=
   exists_simple_step_window g hp hg hper hinj hv
 let I:ℝ:=∫ t in (0:ℝ)..p,(g t 0 - g 0 0) * (deriv g t) 1
 have hI:0 < I:=by simpa [I] using hpos
 let ε:ℝ:=min (min δ (p/2)) (I / (2*p))
 have hp2:0 < p/2:=by linarith
 have hgood:0 < I / (2*p):=by positivity
 have hε:0 < ε:=lt_min (lt_min hδ0 hp2) hgood
 obtain ⟨n,hn,hΔ,hΔη,hΔε,hsimp⟩ :=
   exists_simple_mesh_below g hp hη hε hstep
 let Δ:ℝ:=p / (n:ℝ)
 have hnR:(0:ℝ) < n:=by exact_mod_cast hn
 have hperΔ:(n:ℝ)*Δ = p:=by
   dsimp [Δ]
   field_simp
 have hΔδ:Δ < δ:=lt_of_lt_of_le hΔε
      (le_trans (min_le_left _ _) (min_le_left _ _))
 have hΔp2:Δ < p/2:=lt_of_lt_of_le hΔε
      (le_trans (min_le_left _ _) (min_le_right _ _))
 have hΔlast:Δ < I / (2*p) :=
   lt_of_lt_of_le hΔε (min_le_right _ _)
 have hΔp:Δ < p:=by linarith
 have hy0:g 0 1 < g Δ 1:=hup hΔ hΔδ.le
 have hy1:g (p-Δ) 1 < g 0 1 :=
   hdown (by linarith [hΔδ]) (by linarith [hΔ])
 have hnon:∀i:ℕ,i < n → 0 ≤ g ((i:ℝ)*Δ) 0 - g 0 0:=by
   intro i hi
   have hi0:(0:ℝ) ≤ (i:ℝ)*Δ :=
     mul_nonneg (by exact_mod_cast (Nat.zero_le i)) hΔ.le
   have hinR:(i:ℝ) ≤ (n:ℝ):=by
     exact_mod_cast (le_of_lt hi)
   have hip:(i:ℝ)*Δ ≤ p:=by
     rw [← hperΔ]
     exact mul_le_mul_of_nonneg_right hinR hΔ.le
   linarith [hmin ((i:ℝ)*Δ) ⟨hi0,hip⟩]
 have herror:=curve_xdy_mesh_error g hg hv (g 0 0) Δ hΔ.le n
 have hpform:((n:ℝ)*Δ) = p:=hperΔ
 rw [hpform] at herror
 have herrhalf:(n:ℝ) * Δ^2 < I/2:=by
   have hmul:(n:ℝ) * Δ^2 = p * Δ:=by
     calc
       (n:ℝ) * Δ^2 = ((n:ℝ)*Δ) * Δ:=by ring
       _ = p * Δ:=by rw [hperΔ]
   rw [hmul]
   have hpnon:0 < p:=hp
   have hh:=(mul_lt_mul_of_pos_left hΔlast hpnon)
   have hsimp':p * (I/(2*p)) = I/2:=by
     field_simp
     <;> ring
   rw [hsimp'] at hh
   exact hh
 have herrsmall:(n:ℝ) * Δ^2 < I:=by linarith [herrhalf,hI]
 have hsumpos:0 < ∑ i ∈ Finset.range n,
         (g ((i:ℝ)*Δ) 0 - g 0 0) *
           (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1):=by
   let S:ℝ:=∑ i ∈ Finset.range n,
         (g ((i:ℝ)*Δ) 0 - g 0 0) *
           (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)
   have he:|((∫ t in (0:ℝ)..p,
         (g t 0 - g 0 0) * (deriv g t) 1) - S)| ≤ (n:ℝ)*Δ^2:=by
     simpa [S] using herror
   have hab:=(abs_le.mp he).2
   change 0 < S
   linarith
 have htrappos:0 < ∑ i ∈ Finset.range n,
         (((g ((i:ℝ)*Δ) 0 - g 0 0) +
            (g (((i+1:ℕ):ℝ)*Δ) 0 - g 0 0)) / 2) *
            (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1):=by
   let S:ℝ:=∑ i ∈ Finset.range n,
         (g ((i:ℝ)*Δ) 0 - g 0 0) *
           (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)
   let T:ℝ:=∑ i ∈ Finset.range n,
         (((g ((i:ℝ)*Δ) 0 - g 0 0) +
            (g (((i+1:ℕ):ℝ)*Δ) 0 - g 0 0)) / 2) *
            (g (((i+1:ℕ):ℝ)*Δ) 1 - g ((i:ℝ)*Δ) 1)
   have he:|((∫ t in (0:ℝ)..p,
         (g t 0 - g 0 0) * (deriv g t) 1) - S)| ≤ (n:ℝ)*Δ^2:=by
     simpa [S] using herror
   have hcorr:|T-S| ≤ (n:ℝ)*Δ^2/2:=by
     simpa [T,S] using
       (curve_trapezoid_sub_left_le g hg hv (g 0 0) Δ hΔ.le n)
   have he':=(abs_le.mp he).2
   have hc':=(abs_le.mp hcorr).1
   change 0 < T
   have:0 < I:=hI
   dsimp [I] at this herrhalf ⊢
   linarith
 refine ⟨n,hn,?_⟩
 dsimp
 refine ⟨hΔ,hΔδ,hy0,hy1,hnon,?_,hsumpos,htrappos⟩
 intro i j hij hjn l m l0 l1 m0 m1
 exact hsimp i j hij hjn l m l0 l1 m0 m1
end H
namespace H
open scoped BigOperators
lemma trapezoid_eq_half_det (X Y:ℕ → ℝ) (n:ℕ)
   (hX:X n = X 0) (hY:Y n = Y 0) :
   (∑ i ∈ Finset.range n,
      ((X i + X (i+1))/2) * (Y (i+1) - Y i)) =
     (∑ i ∈ Finset.range n,
        (X i * Y (i+1) - Y i * X (i+1))) / 2:=by
 let A:ℕ → ℝ:=fun i =>
      ((X i + X (i+1))/2) * (Y (i+1) - Y i)
 let D:ℕ → ℝ:=fun i => X i * Y (i+1) - Y i * X (i+1)
 let Z:ℕ → ℝ:=fun i => X i * Y i
 let C:ℕ → ℝ:=fun i => (Z (i+1) - Z i) / 2
 have hpoint (i:ℕ):A i = D i / 2 + C i:=by
   dsimp [A,D,C,Z]
   ring
 have hZ:Z n = Z 0:=by simp [Z,hX,hY]
 have hC:(∑ i ∈ Finset.range n,C i) = 0:=by
   dsimp [C]
   rw [← Finset.sum_div]
   rw [Finset.sum_range_sub Z n]
   rw [hZ]
   norm_num
 change (∑ i ∈ Finset.range n,A i) =
     (∑ i ∈ Finset.range n,D i) / 2
 calc
   (∑ i ∈ Finset.range n,A i) =
       ∑ i ∈ Finset.range n,(D i / 2 + C i):=by
         apply Finset.sum_congr rfl
         intro i hi
         exact hpoint i
   _ = (∑ i ∈ Finset.range n,D i / 2) +
         (∑ i ∈ Finset.range n,C i):=by
           exact Finset.sum_add_distrib
   _ = (∑ i ∈ Finset.range n,D i) / 2:=by
           rw [hC,← Finset.sum_div]
           ring
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/MeshReduction.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/SweepArea.lean
set_option linter.all false
namespace H
open MeasureTheory Set Real
open scoped BigOperators Interval
noncomputable section
def ST (X Y:ℕ → ℝ) (i:ℕ) (w:ℝ):ℝ :=
 if hu:Y i < Y (i+1) then
   (Set.Ioo (Y i) (Y (i+1))).indicator (SX X Y i) w
 else if hd:Y (i+1) < Y i then
   (Set.Ioo (Y (i+1)) (Y i)).indicator (fun z => - SX X Y i z) w
 else 0
def SV (X Y:ℕ → ℝ) (n:ℕ) (w:ℝ):ℝ :=
 ∑ i ∈ Finset.range n,ST X Y i w
lemma continuous_sliceX (X Y:ℕ → ℝ) (i:ℕ) :
   Continuous (SX X Y i):=by
 change Continuous (fun z:ℝ => (1 - (z - Y i) / (Y (i+1) - Y i)) * X i +
          ((z - Y i) / (Y (i+1) - Y i)) * X (i+1))
 fun_prop
lemma sliceTerm_eq_up {X Y:ℕ → ℝ} {i:ℕ} {w:ℝ}
   (h:Y i < w) (h':w < Y (i+1)) :
   ST X Y i w = SX X Y i w:=by
 have hu:Y i < Y (i+1):=lt_trans h h'
 simp [ST,hu,Set.indicator_of_mem (show w ∈ Set.Ioo (Y i) (Y (i+1)) from ⟨h,h'⟩)]
lemma sliceTerm_eq_down {X Y:ℕ → ℝ} {i:ℕ} {w:ℝ}
   (h:Y (i+1) < w) (h':w < Y i) :
   ST X Y i w = - SX X Y i w:=by
 have hd:Y (i+1) < Y i:=lt_trans h h'
 have hu:¬ Y i < Y (i+1):=not_lt_of_ge (le_of_lt hd)
 simp [ST,hu,hd,Set.indicator_of_mem (show w ∈ Set.Ioo (Y (i+1)) (Y i) from ⟨h,h'⟩)]
lemma sliceTerm_eq_zero {X Y:ℕ → ℝ} {i:ℕ} {w:ℝ}
   (h:¬ SA Y i w):ST X Y i w = 0:=by
 unfold SA at h
 by_cases hu:Y i < Y (i+1)
 · have hn:w ∉ Set.Ioo (Y i) (Y (i+1)):=by
     intro hh
     exact h (Or.inl hh)
   simp [ST,hu,Set.indicator,Set.piecewise,hn]
 · by_cases hd:Y (i+1) < Y i
   · have hn:w ∉ Set.Ioo (Y (i+1)) (Y i):=by
       intro hh; exact h (Or.inr hh)
     simp [ST,hu,hd,Set.indicator,Set.piecewise,hn]
   · simp [ST,hu,hd]
lemma integrable_sliceTerm (X Y:ℕ → ℝ) (i:ℕ) :
   Integrable (ST X Y i):=by
 classical
 by_cases hu:Y i < Y (i+1)
 · have hcont:=continuous_sliceX X Y i
   have hI:IntegrableOn (SX X Y i) (Set.Icc (Y i) (Y (i+1))) :=
     hcont.continuousOn.integrableOn_Icc
   have hIo:IntegrableOn (SX X Y i) (Set.Ioo (Y i) (Y (i+1))) :=
     (integrableOn_Icc_iff_integrableOn_Ioo).1 hI
   have hInt:Integrable
       ((Set.Ioo (Y i) (Y (i+1))).indicator (SX X Y i)) :=
     (integrable_indicator_iff measurableSet_Ioo).2 hIo
   have he:ST X Y i =
       (Set.Ioo (Y i) (Y (i+1))).indicator (SX X Y i):=by
     funext w
     simp [ST,hu]
   rw [he]
   exact hInt
 · by_cases hd:Y (i+1) < Y i
   · have hcont:Continuous (fun z => - SX X Y i z) :=
       (continuous_sliceX X Y i).neg
     have hI:IntegrableOn (fun z => - SX X Y i z)
         (Set.Icc (Y (i+1)) (Y i)):=hcont.continuousOn.integrableOn_Icc
     have hIo:IntegrableOn (fun z => - SX X Y i z)
         (Set.Ioo (Y (i+1)) (Y i)) :=
       (integrableOn_Icc_iff_integrableOn_Ioo).1 hI
     have hInt:Integrable
         ((Set.Ioo (Y (i+1)) (Y i)).indicator (fun z => - SX X Y i z)) :=
       (integrable_indicator_iff measurableSet_Ioo).2 hIo
     have he:ST X Y i =
         (Set.Ioo (Y (i+1)) (Y i)).indicator (fun z => - SX X Y i z):=by
       funext w; simp [ST,hu,hd]
     rw [he]
     exact hInt
   · have he:ST X Y i = (fun _ => (0:ℝ)):=by
       funext w; simp [ST,hu,hd]
     rw [he]
     exact integrable_zero _ _ _
lemma integrable_sweepValue (X Y:ℕ → ℝ) (n:ℕ) :
   Integrable (SV X Y n):=by
 classical
 unfold SV
 apply MeasureTheory.integrable_finset_sum
 intro i hi
 exact integrable_sliceTerm X Y i
lemma integral_affine_endpoints (a b u v:ℝ) (hab:b - a ≠ 0) :
   (∫ w in a..b,
      ((1-(w-a)/(b-a))*u + ((w-a)/(b-a))*v)) =
      (b-a) * (u+v) / 2:=by
 have hcont1:IntervalIntegrable (fun _:ℝ => u) MeasureTheory.volume a b :=
   continuous_const.intervalIntegrable _ _
 have hcont2:IntervalIntegrable (fun w:ℝ => w * ((v-u)/(b-a))) MeasureTheory.volume a b :=
   (continuous_id.mul continuous_const).intervalIntegrable _ _
 calc
   (∫ w in a..b,
      ((1-(w-a)/(b-a))*u + ((w-a)/(b-a))*v)) =
      ∫ w in a..b,(u - a*((v-u)/(b-a))) + w*((v-u)/(b-a)):=by
       apply intervalIntegral.integral_congr
       intro x hx
       field_simp
       ring
   _ = (∫ w in a..b,(u - a*((v-u)/(b-a)))) +
         (∫ w in a..b,w*((v-u)/(b-a))):=by
       rw [intervalIntegral.integral_add]
       · exact (continuous_const.intervalIntegrable _ _)
       · exact hcont2
   _ = (b-a) * (u - a*((v-u)/(b-a))) +
        ((b^2-a^2)/2)*((v-u)/(b-a)):=by
       rw [intervalIntegral.integral_const]
       simp [intervalIntegral.integral_mul_const,integral_id]
   _ = (b-a) * (u+v) / 2:=by
       field_simp
       ring
lemma integral_indicator_Ioo_affine (a b:ℝ) (g:ℝ → ℝ)
   (hab:a ≤ b) :
   (∫ w,(Set.Ioo a b).indicator g w) = ∫ w in a..b,g w:=by
 rw [MeasureTheory.integral_indicator measurableSet_Ioo]
 rw [← MeasureTheory.integral_Icc_eq_integral_Ioo]
 rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
 rw [← intervalIntegral.integral_of_le hab]
lemma integral_sliceTerm (X Y:ℕ → ℝ) (i:ℕ) :
   (∫ w,ST X Y i w) =
      (Y (i+1) - Y i) * (X i + X (i+1)) / 2:=by
 classical
 by_cases hu:Y i < Y (i+1)
 · have hne:Y (i+1) - Y i ≠ 0:=by linarith
   have he:ST X Y i =
       (Set.Ioo (Y i) (Y (i+1))).indicator (SX X Y i):=by
     funext w; simp [ST,hu]
   rw [he]
   rw [integral_indicator_Ioo_affine _ _ _ hu.le]
   have hform:=integral_affine_endpoints
       (Y i) (Y (i+1)) (X i) (X (i+1)) hne
   simpa [SX,SP] using hform
 · by_cases hd:Y (i+1) < Y i
   · have hne:Y i - Y (i+1) ≠ 0:=by linarith
     have he:ST X Y i = (Set.Ioo (Y (i+1)) (Y i)).indicator
           (fun w => - SX X Y i w):=by
       funext w; simp [ST,hu,hd]
     rw [he]
     rw [integral_indicator_Ioo_affine _ _ _ hd.le]
     have hform:=integral_affine_endpoints
        (Y (i+1)) (Y i) (- X (i+1)) (- X i) hne
     have hne':Y (i+1) - Y i ≠ 0:=by linarith
     calc
       (∫ w in Y (i+1)..Y i,- SX X Y i w) =
           ∫ w in Y (i+1)..Y i,
            ((1-(w-Y (i+1))/(Y i-Y (i+1)))*(-X (i+1)) +
              ((w-Y (i+1))/(Y i-Y (i+1)))*(-X i)):=by
             apply intervalIntegral.integral_congr
             intro x hx
             dsimp [SX,SP]
             field_simp
             ring
       _ = (Y i - Y (i+1)) * (- X (i+1) + - X i) / 2:=hform
       _ = (Y (i+1) - Y i) * (X i + X (i+1)) / 2:=by ring
   · have heq:Y (i+1) = Y i:=le_antisymm (le_of_not_gt hu) (le_of_not_gt hd)
     simp [ST,hu,hd,heq]
lemma integral_sweepValue (X Y:ℕ → ℝ) (n:ℕ) :
   (∫ w,SV X Y n w) =
      ∑ i ∈ Finset.range n,
         (Y (i+1) - Y i) * (X i + X (i+1)) / 2:=by
 classical
 unfold SV
 rw [MeasureTheory.integral_finset_sum]
 · exact Finset.sum_congr rfl (fun i hi => integral_sliceTerm X Y i)
 · intro i hi
   exact integrable_sliceTerm X Y i
def UE (Y:ℕ → ℝ) (n:ℕ) (w:ℝ):Finset ℕ :=
 (Finset.range n).filter (fun i => Y i < w ∧ w < Y (i+1))
def DE (Y:ℕ → ℝ) (n:ℕ) (w:ℝ):Finset ℕ :=
 (Finset.range n).filter (fun i => Y (i+1) < w ∧ w < Y i)
lemma mem_upEdges {Y:ℕ → ℝ} {n i:ℕ} {w:ℝ} :
   i ∈ UE Y n w ↔ i < n ∧ Y i < w ∧ w < Y (i+1):=by
 simp [UE,and_assoc]
lemma mem_downEdges {Y:ℕ → ℝ} {n i:ℕ} {w:ℝ} :
   i ∈ DE Y n w ↔ i < n ∧ Y (i+1) < w ∧ w < Y i:=by
 simp [DE,and_assoc]
lemma sweepValue_eq_up_sub_down (X Y:ℕ → ℝ) (n:ℕ) (w:ℝ) :
   SV X Y n w =
     (∑ i ∈ UE Y n w,SX X Y i w) -
     (∑ i ∈ DE Y n w,SX X Y i w):=by
 classical
 rw [show SV X Y n w = ∑ i ∈ Finset.range n,ST X Y i w by rfl]
 rw [sub_eq_add_neg,← Finset.sum_neg_distrib]
 rw [UE,DE,Finset.sum_filter,Finset.sum_filter,
     ← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro i hi
 by_cases h1:Y i < w ∧ w < Y (i+1)
 · by_cases h2:Y (i+1) < w ∧ w < Y i
   · simp [h1,h2]
     exfalso; linarith [h1.1,h1.2,h2.1,h2.2]
   · simp [h1,h2]
     rw [sliceTerm_eq_up h1.1 h1.2]
 · by_cases h2:Y (i+1) < w ∧ w < Y i
   · simp [h1,h2]
     rw [sliceTerm_eq_down h2.1 h2.2]
   · simp [h1,h2]
     have hn:¬ SA Y i w:=by
       intro hh; exact (hh.elim h1 h2)
     rw [sliceTerm_eq_zero hn]
lemma det_nonpos_of_regular_sweep
   (X Y:ℕ → ℝ) (n:ℕ)
   (hX:X n = X 0) (hY:Y n = Y 0)
   (hreg:∀(w:ℝ),(∀i:ℕ,i < n → Y i ≠ w) → SV X Y n w ≤ 0) :
   (∑ i ∈ Finset.range n,
      (X i * Y (i+1) - Y i * X (i+1))) ≤ 0:=by
 classical
 let S:Finset ℝ:=(Finset.range n).image (fun i => Y i)
 have hS0:MeasureTheory.volume (↑S:Set ℝ) = 0 :=
   (S.finite_toSet.measure_zero _)
 have haeS:∀ᵐ w:ℝ ∂MeasureTheory.volume,w ∉ (↑S:Set ℝ):=by
   apply (MeasureTheory.ae_iff).2
   simpa using hS0
 have hae:∀ᵐ w:ℝ ∂MeasureTheory.volume,SV X Y n w ≤ (0:ℝ):=by
   filter_upwards [haeS] with w hw
   apply hreg w
   intro i hi he
   have hm:Y i ∈ S:=Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩
   have:w ∈ (↑S:Set ℝ):=by simpa [he] using hm
   exact (hw this).elim
 have hInt:(∫ w:ℝ,SV X Y n w) ≤ (0:ℝ):=by
   have hh:=MeasureTheory.integral_mono_ae
      (integrable_sweepValue X Y n)
      (MeasureTheory.integrable_zero ℝ ℝ MeasureTheory.volume) hae
   simpa using hh
 rw [integral_sweepValue] at hInt
 have htrap:=trapezoid_eq_half_det X Y n hX hY
 have he:(∑ i ∈ Finset.range n,
         (Y (i+1) - Y i) * (X i + X (i+1)) / 2) =
       (∑ i ∈ Finset.range n,
         ((X i + X (i+1))/2) * (Y (i+1) - Y i)):=by
   apply Finset.sum_congr rfl
   intro i hi
   ring
 rw [he,htrap] at hInt
 linarith
end
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/SweepArea.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Events.lean
set_option linter.all false
namespace H
open scoped BigOperators
open scoped Classical
section Counts
variable (Y:ℕ → ℝ) (n:ℕ) (w:ℝ)
private noncomputable def bel (Y:ℕ → ℝ) (w:ℝ) (i:ℕ):ℤ :=
 if Y i < w then 1 else 0
private lemma step_regular {Y:ℕ → ℝ} {n:ℕ} {w:ℝ}
   (hreg:∀i,i ≤ n → Y i ≠ w) (i:ℕ) (hi:i < n) :
   bel Y w i - bel Y w (i+1) =
     (if Y i < w ∧ w < Y (i+1) then (1:ℤ)
      else if Y (i+1) < w ∧ w < Y i then (-1:ℤ) else 0):=by
 have hni:=hreg i hi.le
 have hni1:=hreg (i+1) (by omega)
 dsimp [bel]
 by_cases a:Y i < w
 · by_cases b:Y (i+1) < w
   ·
     have c:¬ w < Y (i+1):=not_lt_of_ge (le_of_lt b)
     simp [a,b,c,(le_of_lt a)]
   · have wb:w < Y (i+1):=by
       have hb:w ≤ Y (i+1):=le_of_not_gt b
       exact lt_of_le_of_ne hb (Ne.symm hni1)
     have nwa:¬ w < Y i:=not_lt_of_ge (le_of_lt a)
     simp [a,b,wb,nwa]
 · have wa:w < Y i:=by
     have ha:w ≤ Y i:=le_of_not_gt a
     exact lt_of_le_of_ne ha (Ne.symm hni)
   by_cases b:Y (i+1) < w
   · have nwib:¬ w < Y (i+1):=not_lt_of_ge (le_of_lt b)
     simp [a,b,wa,nwib]
   · have wb:w < Y (i+1):=by
       have hb:w ≤ Y (i+1):=le_of_not_gt b
       exact lt_of_le_of_ne hb (Ne.symm hni1)
     simp [a,b,wa,wb]
private lemma telescope_bel {Y:ℕ → ℝ} {n:ℕ} {w:ℝ} :
   (∑ i ∈ Finset.range n,
      (bel Y w i - bel Y w (i+1))) = bel Y w 0 - bel Y w n:=by
 induction n with
 | zero => simp
 | succ n ih =>
     rw [Finset.sum_range_succ]
     rw [ih]
     ring
end Counts
end H
namespace H
open scoped BigOperators
lemma card_up_eq_card_down_regular
   (Y:ℕ → ℝ) (n:ℕ) (w:ℝ)
   (hclose:Y n = Y 0)
   (hreg:∀i,i ≤ n → Y i ≠ w) :
   (UE Y n w).card = (DE Y n w).card:=by
 classical
 have htel:=telescope_bel (Y:=Y) (n:=n) (w:=w)
 have hz:bel Y w 0 - bel Y w n = 0:=by
   dsimp [bel]
   rw [hclose]
   ring
 have hsumzero:(∑ i ∈ Finset.range n,
     ((if Y i < w ∧ w < Y (i+1) then (1:ℤ)
      else if Y (i+1) < w ∧ w < Y i then (-1:ℤ) else 0))) = 0:=by
   calc
     _ = (∑ i ∈ Finset.range n,
             (bel Y w i - bel Y w (i+1))):=by
             apply Finset.sum_congr rfl
             intro i hi
             exact (step_regular hreg i (Finset.mem_range.mp hi)).symm
     _ = bel Y w 0 - bel Y w n:=htel
     _ = 0:=hz
 have hup:(∑ i ∈ Finset.range n,
      (if Y i < w ∧ w < Y (i+1) then (1:ℤ) else 0)) =
       ((UE Y n w).card:ℤ):=by
   simpa [UE] using
     (Finset.sum_boole (R:=ℤ)
       (fun i:ℕ => Y i < w ∧ w < Y (i+1)) (Finset.range n))
 have hdown:(∑ i ∈ Finset.range n,
      (if Y (i+1) < w ∧ w < Y i then (1:ℤ) else 0)) =
       ((DE Y n w).card:ℤ):=by
   simpa [DE] using
     (Finset.sum_boole (R:=ℤ)
       (fun i:ℕ => Y (i+1) < w ∧ w < Y i) (Finset.range n))
 have hrewrite:(∑ i ∈ Finset.range n,
     ((if Y i < w ∧ w < Y (i+1) then (1:ℤ)
      else if Y (i+1) < w ∧ w < Y i then (-1:ℤ) else 0))) =
       (∑ i ∈ Finset.range n,
          (if Y i < w ∧ w < Y (i+1) then (1:ℤ) else 0)) -
       (∑ i ∈ Finset.range n,
          (if Y (i+1) < w ∧ w < Y i then (1:ℤ) else 0)):=by
   rw [← Finset.sum_sub_distrib]
   apply Finset.sum_congr rfl
   intro i hi
   by_cases a:Y i < w ∧ w < Y (i+1)
   · have nb:¬ (Y (i+1) < w ∧ w < Y i):=by
       intro hb; linarith [a.1,a.2,hb.1,hb.2]
     simp [a,nb]
   · by_cases b:Y (i+1) < w ∧ w < Y i
     · simp [a,b]
     · simp [a,b]
 rw [hrewrite,hup,hdown] at hsumzero
 have heqz:((UE Y n w).card:ℤ) =
     ((DE Y n w).card:ℤ):=by linarith
 exact_mod_cast heqz
end H
namespace H
open scoped BigOperators
lemma exists_right_matching_of_suffix
   (U D:Finset ℕ) (v:ℕ → ℝ)
   (hsuf:∀i ∈ U,
     (U.filter (fun k => v i ≤ v k)).card ≤
       (D.filter (fun k => v i ≤ v k)).card) :
   ∃g:ℕ → ℕ,
     Set.InjOn g (↑U:Set ℕ) ∧
     ∀i ∈ U,g i ∈ D ∧ v i ≤ v (g i):=by
 classical
 let Uty:={i:ℕ // i ∈ U}
 let t:Uty → Finset ℕ:=fun i => D.filter (fun j => v i.1 ≤ v j)
 have hHall:∀s:Finset Uty,s.card ≤ (s.biUnion t).card:=by
   intro s
   by_cases se:s.Nonempty
   · obtain ⟨a,ha,hmin⟩:=Finset.exists_min_image s (fun i:Uty => v i.1) se
     have hasU:a.1 ∈ U:=a.2
     have hsubU:s.card ≤ (U.filter (fun k => v a.1 ≤ v k)).card:=by
       let emb:Uty ↪ ℕ:=⟨(fun i => i.1),(by intro i j h; exact Subtype.ext h)⟩
       have hmaps:s.map emb ⊆ U.filter (fun k => v a.1 ≤ v k):=by
         intro k hk
         rcases (Finset.mem_map.mp hk) with ⟨x,hx,rfl⟩
         have hxle:=hmin x hx
         change x.1 ∈ U.filter (fun k => v a.1 ≤ v k)
         exact Finset.mem_filter.mpr ⟨x.2,hxle⟩
       calc
         s.card = (s.map emb).card:=by simp
         _ ≤ (U.filter (fun k => v a.1 ≤ v k)).card :=
           Finset.card_le_card hmaps
     have hDsub:D.filter (fun k => v a.1 ≤ v k) ⊆ s.biUnion t:=by
       intro k hk
       have:k ∈ t a:=by exact hk
       exact Finset.mem_biUnion.mpr ⟨a,ha,this⟩
     exact le_trans (le_trans hsubU (hsuf a.1 a.2))
         (Finset.card_le_card hDsub)
   · have:s = ∅:=Finset.not_nonempty_iff_eq_empty.mp se
     simp [this]
 obtain ⟨f,hf,hfmem⟩ :=
   (Finset.all_card_le_biUnion_card_iff_existsInjective' t).1 hHall
 let g:ℕ → ℕ:=fun i => dite (i ∈ U) (fun h => f (⟨i,h⟩:Uty)) (fun _ => 0)
 refine ⟨g,?_,?_⟩
 · intro i hi j hj eq
   have hi':i ∈ U:=hi
   have hj':j ∈ U:=hj
   have heq:f (⟨i,hi'⟩:Uty) = f (⟨j,hj'⟩:Uty):=by
     simpa [g,hi',hj'] using eq
   have hs:=hf heq
   exact congrArg Subtype.val hs
 · intro i hi
   have hm:=hfmem (⟨i,hi⟩:Uty)
   have hg:g i = f (⟨i,hi⟩:Uty):=by simp [g,hi]
   change f (⟨i,hi⟩:Uty) ∈ D.filter (fun j => v i ≤ v j) at hm
   have hb:=(Finset.mem_filter.mp hm)
   constructor
   · simpa [hg] using hb.1
   · simpa [hg] using hb.2
end H
namespace H
open scoped BigOperators
lemma sweep_nonpos_of_matching_at
   (X Y:ℕ → ℝ) (n:ℕ) (w:ℝ)
   (hnon:∀i,i < n → ∀z,SA Y i z → 0 ≤ SX X Y i z)
   (hw:∃f:ℕ → ℕ,
        Set.InjOn f (↑(UE Y n w):Set ℕ) ∧
        (∀i ∈ UE Y n w,
           f i ∈ DE Y n w ∧
           SX X Y i w ≤ SX X Y (f i) w)) :
   SV X Y n w ≤ 0:=by
 classical
 rcases hw with ⟨f,hf,hprop⟩
 let U:=UE Y n w
 let T:=DE Y n w
 let fi:Finset ℕ:=U.image f
 have hsub:fi ⊆ T:=by
   intro j hj
   rcases Finset.mem_image.mp hj with ⟨i,hi,rfl⟩
   exact (hprop i hi).1
 have hle1:(∑ i ∈ U,SX X Y i w) ≤
     ∑ i ∈ U,SX X Y (f i) w:=by
   apply Finset.sum_le_sum
   intro i hi
   exact (hprop i hi).2
 have hsumfi:(∑ j ∈ fi,SX X Y j w) =
     ∑ i ∈ U,SX X Y (f i) w:=by
   exact Finset.sum_image hf
 have hle2:(∑ j ∈ fi,SX X Y j w) ≤
     ∑ j ∈ T,SX X Y j w:=by
   apply Finset.sum_le_sum_of_subset_of_nonneg hsub
   intro j hj hnot
   have hm:=(mem_downEdges).1 hj
   exact hnon j hm.1 w (Or.inr hm.2)
 rw [sweepValue_eq_up_sub_down]
 change (∑ i ∈ U,SX X Y i w) -
     (∑ i ∈ T,SX X Y i w) ≤ 0
 linarith [hle1,hle2,hsumfi]
end H
namespace H
lemma sliceParam_start {Y:ℕ → ℝ} {i:ℕ}
   (h:Y (i+1) ≠ Y i):SP Y i (Y i) = 0:=by
 dsimp [SP]
 simp
lemma sliceParam_end {Y:ℕ → ℝ} {i:ℕ}
   (h:Y (i+1) ≠ Y i):SP Y i (Y (i+1)) = 1:=by
 dsimp [SP]
 have hd:Y (i+1) - Y i ≠ 0:=sub_ne_zero.mpr h
 exact div_self hd
lemma sliceX_start {X Y:ℕ → ℝ} {i:ℕ}
   (h:Y (i+1) ≠ Y i):SX X Y i (Y i) = X i:=by
 dsimp [SX]
 simp [sliceParam_start h]
lemma sliceX_end {X Y:ℕ → ℝ} {i:ℕ}
   (h:Y (i+1) ≠ Y i):SX X Y i (Y (i+1)) = X (i+1):=by
 dsimp [SX]
 simp [sliceParam_end h]
lemma slice_vertex_ne_of_halfopen
   (X Y:ℕ → ℝ) {n:ℕ}
   (edge:∀a b:ℕ,a < b → b < n → ∀l m:ℝ,0 ≤ l → l < 1 → 0 ≤ m → m < 1 → ((1-l)*X a + l*X (a+1) ≠ (1-m)*X b + m*X (b+1)) ∨
         ((1-l)*Y a + l*Y (a+1) ≠ (1-m)*Y b + m*Y (b+1)))
   {a k:ℕ} (ha:a < n) (hk:k < n) (hak:a ≠ k)
   {z:ℝ} (hz:z = Y k)
   (hact:SA Y a z) :
   SX X Y a (Y k) ≠ X k:=by
 classical
 subst z
 have hp:=param_pos_lt_one hact
 have hy:=slice_height hact
 by_cases hlt:a < k
 · have hh:=edge a k hlt hk (SP Y a (Y k)) 0 hp.1.le hp.2
             (by norm_num) (by norm_num)
   rcases hh with hh | hh
   · simpa [SX] using hh
   · simp at hh
     exact (hh hy).elim
 · have hka:k < a:=by omega
   have hh:=edge k a hka ha 0 (SP Y a (Y k))
                 (by norm_num) (by norm_num) hp.1.le hp.2
   rcases hh with hh | hh
   · have:X k ≠ SX X Y a (Y k):=by simpa [SX] using hh
     exact Ne.symm this
   · have hh':Y k ≠ (1 - SP Y a (Y k)) * Y a +
                  SP Y a (Y k) * Y (a+1):=by simpa using hh
     exact (hh' hy.symm).elim
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Events.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Prefix.lean
set_option linter.all false

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Prefix.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/PrefixInvariant.lean
set_option linter.all false
namespace H
open scoped BigOperators
open Filter Set Topology Classical
noncomputable def PT (X Y:ℕ → ℝ) (e j:ℕ) (z:ℝ):ℤ :=
  if SX X Y j z < SX X Y e z then
    if (Y j ≤ z ∧ z < Y (j+1)) then 1
    else if (Y (j+1) ≤ z ∧ z < Y j) then -1 else 0
  else 0
noncomputable def pref (X Y:ℕ → ℝ) (n e:ℕ) (z:ℝ):ℤ :=
  ∑ j ∈ Finset.range n,PT X Y e j z
lemma continuous_slice (X Y:ℕ → ℝ) (j:ℕ) :
    Continuous (SX X Y j):=by
  unfold SX SP
  fun_prop
private lemma eventually_lt_or_nlt
    (f g:ℝ → ℝ) {z:ℝ} (hc:Continuous f) (hd:Continuous g)
    (hne:f z ≠ g z) :
    ∀ᶠ u in 𝓝 z,(f u < g u) = (f z < g z):=by
  rcases lt_or_gt_of_ne hne with h | h
  · filter_upwards [hc.continuousAt.eventually_lt hd.continuousAt h] with u hu
    simp [hu,h]
  · have ev:=hd.continuousAt.eventually_lt hc.continuousAt h
    filter_upwards [ev] with u hu
    have h1:¬ f u < g u:=not_lt_of_ge (le_of_lt hu)
    have h0:¬ f z < g z:=not_lt_of_ge (le_of_lt h)
    simp [h1,h0]
private lemma eventually_not_between {a b z:ℝ}
    (hz:¬(a ≤ z ∧ z < b)) (hz':¬(b ≤ z ∧ z < a))
    (hna:a ≠ z) (hnb:b ≠ z) :
    ∀ᶠ u in 𝓝 z,(¬(a ≤ u ∧ u < b)) ∧ (¬(b ≤ u ∧ u < a)):=by
  have ea:∀ᶠ u in 𝓝 z,(a < u) = (a < z):=by
    exact eventually_lt_or_nlt (fun _ => a) (fun u => u)
      (by fun_prop) (by fun_prop) hna
  have eaz:∀ᶠ u in 𝓝 z,(u < a) = (z < a):=by
    exact eventually_lt_or_nlt (fun u => u) (fun _ => a)
      (by fun_prop) (by fun_prop) hna.symm
  have eb:∀ᶠ u in 𝓝 z,(b < u) = (b < z):=by
    exact eventually_lt_or_nlt (fun _ => b) (fun u => u)
      (by fun_prop) (by fun_prop) hnb
  have ebz:∀ᶠ u in 𝓝 z,(u < b) = (z < b):=by
    exact eventually_lt_or_nlt (fun u => u) (fun _ => b)
      (by fun_prop) (by fun_prop) hnb.symm
  filter_upwards [ea,eaz,eb,ebz] with u ha ha' hb hb'
  have hanu:a ≠ u:=by
    intro hh
    subst u
    have h1:¬ a < z:=by simpa using ha
    have h2:¬ z < a:=by simpa using ha'
    exact (hna (le_antisymm (le_of_not_gt h2) (le_of_not_gt h1))).elim
  have hbnu:b ≠ u:=by
    intro hh
    subst u
    have h1:¬ b < z:=by simpa using hb
    have h2:¬ z < b:=by simpa using hb'
    exact (hnb (le_antisymm (le_of_not_gt h2) (le_of_not_gt h1))).elim
  constructor
  · intro hbet
    have h0:a < u:=lt_of_le_of_ne hbet.1 hanu
    have h1:u < b:=hbet.2
    have hz0:a < z:=by simpa [ha] using h0
    have hz1:z < b:=by simpa [hb'] using h1
    exact hz ⟨hz0.le,hz1⟩
  · intro hbet
    have h0:b < u:=lt_of_le_of_ne hbet.1 hbnu
    have h1:u < a:=hbet.2
    have hz0:b < z:=by simpa [hb] using h0
    have hz1:z < a:=by simpa [ha'] using h1
    exact hz' ⟨hz0.le,hz1⟩
lemma prefTerm_eventually_of_noend
    (X Y:ℕ → ℝ) {e j:ℕ} {z:ℝ}
    (hna:Y j ≠ z) (hnb:Y (j+1) ≠ z)
    (hene:j = e ∨
      (SA Y j z → SX X Y j z ≠ SX X Y e z)) :
    ∀ᶠ u in 𝓝 z,PT X Y e j u = PT X Y e j z:=by
  classical
  rcases hene with heq | hnee
  · subst j
    simp [PT]
  · by_cases hu:Y j ≤ z ∧ z < Y (j+1)
    · have hlt:Y j < z:=lt_of_le_of_ne hu.1 hna
      have hU:∀ᶠ u in 𝓝 z,Y j ≤ u ∧ u < Y (j+1):=by
        have e1:=(continuousAt_const.eventually_lt continuousAt_id hlt)
        have e2:=(continuousAt_id.eventually_lt continuousAt_const hu.2)
        filter_upwards [e1,e2] with t ht ht'
        simpa using (show Y j ≤ id t ∧ id t < Y (j+1) from ⟨ht.le,ht'⟩)
      have hact:SA Y j z:=Or.inl ⟨hlt,hu.2⟩
      have hnside:=hnee hact
      have eside:=eventually_lt_or_nlt (SX X Y j) (SX X Y e)
            (continuous_slice X Y j) (continuous_slice X Y e) hnside
      filter_upwards [hU,eside] with t ht hs
      simp [PT,ht,hu,hs]
    · by_cases hd:Y (j+1) ≤ z ∧ z < Y j
      · have hlt:Y (j+1) < z:=lt_of_le_of_ne hd.1 hnb
        have hD:∀ᶠ u in 𝓝 z,Y (j+1) ≤ u ∧ u < Y j:=by
          have e1:=(continuousAt_const.eventually_lt continuousAt_id hlt)
          have e2:=(continuousAt_id.eventually_lt continuousAt_const hd.2)
          filter_upwards [e1,e2] with t ht ht'
          simpa using (show Y (j+1) ≤ id t ∧ id t < Y j from ⟨ht.le,ht'⟩)
        have hact:SA Y j z:=Or.inr ⟨hlt,hd.2⟩
        have hnside:=hnee hact
        have eside:=eventually_lt_or_nlt (SX X Y j) (SX X Y e)
              (continuous_slice X Y j) (continuous_slice X Y e) hnside
        filter_upwards [hD,eside] with t ht hs
        have hnu0:¬ (Y j ≤ t ∧ t < Y (j+1)):=by intro h; linarith
        simp [PT,ht,hu,hd,hs,hnu0]
      · have ev:=eventually_not_between hu hd hna hnb
        filter_upwards [ev] with t ht
        simp [PT,ht.1,ht.2,hu,hd]
noncomputable def hstep (a b z:ℝ):ℤ :=
  if (a ≤ z ∧ z < b) then 1 else if (b ≤ z ∧ z < a) then -1 else 0
lemma step_pair_eventually (A B z:ℝ) (ha:A ≠ z) (hb:B ≠ z) :
    ∀ᶠ u in 𝓝 z,
      hstep A z u + hstep z B u = hstep A z z + hstep z B z:=by
  rcases lt_or_gt_of_ne ha with haz | haz <;>
    rcases lt_or_gt_of_ne hb with hbz | hbz
  · have eA:=(continuousAt_const.eventually_lt continuousAt_id haz)
    have eB:=(continuousAt_const.eventually_lt continuousAt_id hbz)
    filter_upwards [eA,eB] with u hu hv
    simp at hu hv
    rcases lt_trichotomy u z with hlt|heq|hgt
    · have au:=(le_of_lt hu); have bu:=(le_of_lt hv)
      have nz:¬ z ≤ u:=not_le_of_gt hlt
      have nua:¬ u < A:=not_lt_of_ge au
      have nub:¬ u < B:=not_lt_of_ge bu
      have nza:¬ z < A:=not_lt_of_ge haz.le
      have nzb:¬ z < B:=not_lt_of_ge hbz.le
      simp [hstep,au,bu,nz,nua,nub,nza,nzb,hlt]
    · subst u; rfl
    · have nzA:¬ u < A:=not_lt_of_ge (le_trans haz.le hgt.le)
      have nzB:¬ u < B:=not_lt_of_ge (le_trans hbz.le hgt.le)
      have nuz:¬ u < z:=not_lt_of_ge hgt.le
      have nza:¬ z < A:=not_lt_of_ge haz.le
      have nzb:¬ z < B:=not_lt_of_ge hbz.le
      simp [hstep,nzA,nzB,nuz,nza,nzb,hgt]
  · have eA:=(continuousAt_const.eventually_lt continuousAt_id haz)
    have eB:=(continuousAt_id.eventually_lt continuousAt_const hbz)
    filter_upwards [eA,eB] with u hu hv
    simp at hu hv
    have au:A ≤ u:=le_of_lt hu
    have ub:¬ B ≤ u:=not_le_of_gt hv
    have nUA:¬ u < A:=not_lt_of_ge au
    have nBU:¬ B < u:=not_lt_of_ge hv.le
    have nza:¬ z < A:=not_lt_of_ge haz.le
    rcases lt_trichotomy u z with hlt|heq|hgt
    · have nz:¬ z ≤ u:=not_le_of_gt hlt
      simp [hstep,au,ub,nUA,nBU,nza,nz,hlt,hbz]
    · subst u; rfl
    · have nuz:¬ u < z:=not_lt_of_ge hgt.le
      simp [hstep,au,ub,nUA,nBU,nza,nuz,hgt,hbz]
  · have eA:=(continuousAt_id.eventually_lt continuousAt_const haz)
    have eB:=(continuousAt_const.eventually_lt continuousAt_id hbz)
    filter_upwards [eA,eB] with u hu hv
    simp at hu hv
    have nAu:¬ A ≤ u:=not_le_of_gt hu
    have bu:B ≤ u:=le_of_lt hv
    have nUa:¬ A < u:=not_lt_of_ge hu.le
    have nub:¬ u < B:=not_lt_of_ge bu
    have nzb:¬ z < B:=not_lt_of_ge hbz.le
    rcases lt_trichotomy u z with hlt|heq|hgt
    · have nz:¬ z ≤ u:=not_le_of_gt hlt
      simp [hstep,nAu,bu,nUa,nub,nzb,nz,hlt,haz]
    · subst u; rfl
    · have nuz:¬ u < z:=not_lt_of_ge hgt.le
      simp [hstep,nAu,bu,nUa,nub,nzb,nuz,hgt,haz]
  · have eA:=(continuousAt_id.eventually_lt continuousAt_const haz)
    have eB:=(continuousAt_id.eventually_lt continuousAt_const hbz)
    filter_upwards [eA,eB] with u hu hv
    simp at hu hv
    have nAu:¬ A ≤ u:=not_le_of_gt hu
    have nBu:¬ B ≤ u:=not_le_of_gt hv
    have nAu':¬ A < u:=not_lt_of_ge hu.le
    have nBu':¬ B < u:=not_lt_of_ge hv.le
    rcases lt_trichotomy u z with hlt|heq|hgt
    · have nz:¬ z ≤ u:=not_le_of_gt hlt
      simp [hstep,nAu,nBu,nAu',nBu',nz,hlt,haz,hbz]
    · subst u; rfl
    · have uzA:u < A:=hu
      have uzB:u < B:=hv
      have nuz:¬ u < z:=not_lt_of_ge hgt.le
      simp [hstep,nAu,nBu,nAu',nBu',nuz,hgt.le,haz,hbz,uzA,uzB]
end H
namespace H
open scoped BigOperators
open Classical
lemma pref_eq_counts (X Y:ℕ → ℝ) (n e:ℕ) (z:ℝ)
    (hreg: ∀k,k ≤ n → Y k ≠ z) :
 pref X Y n e z =
   (( (UE Y n z).filter (fun j => SX X Y j z < SX X Y e z)).card:ℤ) -
   (( (DE Y n z).filter (fun j => SX X Y j z < SX X Y e z)).card:ℤ):=by
 classical
 have heach:∀j ∈ Finset.range n,
    PT X Y e j z =
      (if (Y j < z ∧ z < Y (j+1)) ∧
           SX X Y j z < SX X Y e z then (1:ℤ) else 0) -
      (if (Y (j+1) < z ∧ z < Y j) ∧
           SX X Y j z < SX X Y e z then (1:ℤ) else 0):=by
  intro j hj
  have hj0:=hreg j (Finset.mem_range.mp hj |>.le)
  have hj1:=hreg (j+1) (by have:=Finset.mem_range.mp hj; omega)
  by_cases hU: Y j < z ∧ z < Y (j+1)
  · have hDn: ¬ (Y (j+1) < z ∧ z < Y j):=by intro h; linarith
    have hu':Y j ≤ z ∧ z < Y (j+1):=⟨hU.1.le,hU.2⟩
    by_cases hxx:SX X Y j z < SX X Y e z <;>
      simp [PT,hU,hDn,hu',hxx]
  · by_cases hD: Y (j+1) < z ∧ z < Y j
    · have hd':Y (j+1) ≤ z ∧ z < Y j:=⟨hD.1.le,hD.2⟩
      have hu':¬ (Y j ≤ z ∧ z < Y (j+1)):=by
        intro h
        have hzlt:Y j < z:=lt_of_le_of_ne h.1 hj0
        exact hU ⟨hzlt,h.2⟩
      by_cases hxx:SX X Y j z < SX X Y e z <;>
        simp [PT,hU,hD,hd',hu',hxx]
    · have hu':¬ (Y j ≤ z ∧ z < Y (j+1)):=by
        intro h; exact hU ⟨lt_of_le_of_ne h.1 hj0,h.2⟩
      have hd':¬ (Y (j+1) ≤ z ∧ z < Y j):=by
        intro h; exact hD ⟨lt_of_le_of_ne h.1 hj1,h.2⟩
      simp [PT,hU,hD,hu',hd']
 rw [pref]
 rw [show (∑ j ∈ Finset.range n,PT X Y e j z) =
      ∑ j ∈ Finset.range n,
       ((if (Y j < z ∧ z < Y (j+1)) ∧ SX X Y j z < SX X Y e z
          then (1:ℤ) else 0) -
        (if (Y (j+1) < z ∧ z < Y j) ∧ SX X Y j z < SX X Y e z
          then (1:ℤ) else 0)) by
        apply Finset.sum_congr rfl; intro j hj
        exact heach j hj]
 rw [Finset.sum_sub_distrib]
 have h1:(∑ j ∈ Finset.range n,
       (if (Y j < z ∧ z < Y (j+1)) ∧ SX X Y j z < SX X Y e z
          then (1:ℤ) else 0)) =
       (((UE Y n z).filter (fun j => SX X Y j z < SX X Y e z)).card:ℤ):=by
   rw [Finset.sum_boole (R:=ℤ)
      (fun j:ℕ => (Y j < z ∧ z < Y (j+1)) ∧ SX X Y j z < SX X Y e z)
      (Finset.range n)]
   apply congrArg (fun s:Finset ℕ => (s.card:ℤ))
   ext j
   simp [UE,and_left_comm,and_assoc]
 have h2:(∑ j ∈ Finset.range n,
       (if (Y (j+1) < z ∧ z < Y j) ∧ SX X Y j z < SX X Y e z
          then (1:ℤ) else 0)) =
       (((DE Y n z).filter (fun j => SX X Y j z < SX X Y e z)).card:ℤ):=by
   rw [Finset.sum_boole (R:=ℤ)
      (fun j:ℕ => (Y (j+1) < z ∧ z < Y j) ∧ SX X Y j z < SX X Y e z)
      (Finset.range n)]
   apply congrArg (fun s:Finset ℕ => (s.card:ℤ))
   ext j
   simp [DE,and_left_comm,and_assoc]
 rw [h1,h2]
lemma prefTerm_eq_step (X Y:ℕ → ℝ) (e j:ℕ) (z:ℝ) :
 PT X Y e j z =
   if SX X Y j z < SX X Y e z then hstep (Y j) (Y (j+1)) z
   else 0:=by
  rfl
lemma incident_terms_eventually
    (X Y:ℕ → ℝ) {e p k:ℕ}
    (hY:Y (p+1) = Y k) (hX:X (p+1) = X k)
    (hp:Y p ≠ Y k) (hk:Y (k+1) ≠ Y k)
    (hne:X k ≠ SX X Y e (Y k)) :
    ∀ᶠ u in nhds (Y k),
      PT X Y e p u + PT X Y e k u =
      PT X Y e p (Y k) + PT X Y e k (Y k):=by
  classical
  have hpden:Y (p+1) ≠ Y p:=by rw [hY]; exact Ne.symm hp
  have hkden:Y (k+1) ≠ Y k:=hk
  have hpval:SX X Y p (Y k) = X k:=by
    rw [← hY,sliceX_end hpden,hX]
  have hkval:SX X Y k (Y k) = X k:=by
    rw [sliceX_start hkden]
  have hnp:SX X Y p (Y k) ≠ SX X Y e (Y k) :=
    hpval.symm ▸ hne
  have hnk:SX X Y k (Y k) ≠ SX X Y e (Y k) :=
    hkval.symm ▸ hne
  have sp:=eventually_lt_or_nlt (SX X Y p) (SX X Y e)
       (continuous_slice X Y p) (continuous_slice X Y e) hnp
  have sk:=eventually_lt_or_nlt (SX X Y k) (SX X Y e)
       (continuous_slice X Y k) (continuous_slice X Y e) hnk
  have st:=step_pair_eventually (Y p) (Y (k+1)) (Y k)
       hp hk
  filter_upwards [sp,sk,st] with u hsp hsk hst
  have flags:(SX X Y p (Y k) < SX X Y e (Y k)) =
               (SX X Y k (Y k) < SX X Y e (Y k)):=by
    rw [hpval,hkval]
  simp only [prefTerm_eq_step]
  have hpflag:(SX X Y p u < SX X Y e u) =
       (SX X Y p (Y k) < SX X Y e (Y k)):=hsp
  have hkflag:(SX X Y k u < SX X Y e u) =
       (SX X Y k (Y k) < SX X Y e (Y k)):=hsk
  by_cases f:SX X Y k (Y k) < SX X Y e (Y k)
  · have fp:SX X Y p (Y k) < SX X Y e (Y k):=by
      exact (Eq.mpr flags) f
    have fpu:SX X Y p u < SX X Y e u:=by
      exact (Eq.mpr hpflag) fp
    have fku:SX X Y k u < SX X Y e u :=
      (Eq.mpr hkflag) f
    simp [fp,f,fpu,fku,hY]
    simpa [hY] using hst
  · have fp:¬ SX X Y p (Y k) < SX X Y e (Y k):=by
      intro hh
      have:SX X Y k (Y k) < SX X Y e (Y k) :=
        (Eq.mp flags) hh
      exact f this
    have fpu:¬ SX X Y p u < SX X Y e u:=by
      intro hh; exact fp ((Eq.mp hpflag) hh)
    have fku:¬ SX X Y k u < SX X Y e u:=by
      intro hh; exact f ((Eq.mp hkflag) hh)
    simp [fp,f,fpu,fku]

end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/PrefixInvariant.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/CyclePrefix.lean
set_option linter.all false
namespace H
open scoped BigOperators
open Set Filter Topology
open Classical
private lemma active_between {Y:ℕ → ℝ} {j:ℕ} {u:ℝ}
   (hlo:min (Y j) (Y (j+1)) < u)
   (hhi:u < max (Y j) (Y (j+1))):SA Y j u:=by
 unfold SA
 rcases le_total (Y j) (Y (j+1)) with h | h
 · have hne:Y j < Y (j+1):=lt_of_le_of_ne h (by
     intro hh; rw [hh] at hlo hhi; simpa using (lt_trans hlo hhi))
   left
   simpa [min_eq_left h,max_eq_right h] using And.intro hlo hhi
 · have hne:Y (j+1) < Y j:=lt_of_le_of_ne h (by
     intro hh; rw [hh] at hlo hhi; simpa using (lt_trans hlo hhi))
   right
   simpa [min_eq_right h,max_eq_left h] using And.intro hlo hhi
private lemma mid_mem (a b:ℝ) (h:a ≠ b) :
   (a+b)/2 ∈ Set.Ioo (min a b) (max a b):=by
 rcases lt_or_gt_of_ne h with h|h
 · simp [min_eq_left h.le,max_eq_right h.le]
   constructor <;> linarith
 · simp [min_eq_right h.le,max_eq_left h.le]
   constructor <;> linarith
noncomputable def EP (X Y:ℕ → ℝ) (n e:ℕ):ℤ :=
 pref X Y n e ((Y e + Y (e+1))/2)
lemma edgePref_eq
   (X Y:ℕ → ℝ) (n:ℕ) (hn:3 ≤ n)
   (hclX:X n = X 0) (hclY:Y n = Y 0)
   (hdiff:∀i,i < n → ∀j,j < n → i ≠ j → Y i ≠ Y j)
   (hside:∀j,j < n → Y (j+1) ≠ Y j)
   (hopenne:∀{a b:ℕ},a < n → b < n → a ≠ b → ∀{u:ℝ},SA Y a u → SA Y b u → SX X Y a u ≠ SX X Y b u)
   (hvert:∀{a k:ℕ},a < n → k < n → a ≠ k → SA Y a (Y k) → SX X Y a (Y k) ≠ X k)
   {e:ℕ} (he:e < n) {u:ℝ}
   (hu:SA Y e u) :
   pref X Y n e u = EP X Y n e:=by
 classical
 have hne_e:=hside e he
 have huI:u ∈ Set.Ioo (min (Y e) (Y (e+1))) (max (Y e) (Y (e+1))):=by
   rcases hu with hu|hu
   · simpa [min_eq_left (le_of_lt (lt_trans hu.1 hu.2)),
         max_eq_right (le_of_lt (lt_trans hu.1 hu.2))] using hu
   · simpa [min_eq_right (le_of_lt (lt_trans hu.1 hu.2)),
         max_eq_left (le_of_lt (lt_trans hu.1 hu.2))] using hu
 let I:Set ℝ:=Set.Ioo (min (Y e) (Y (e+1))) (max (Y e) (Y (e+1)))
 have hact (z:I):SA Y e (z:ℝ) :=
   active_between z.property.1 z.property.2
 have novtx (z:ℝ) (hzact:SA Y e z)
     (hnov:∀k,k < n → Y k ≠ z) :
     ∀ᶠ t in nhds z,pref X Y n e t = pref X Y n e z:=by
   have hnov':∀k,k ≤ n → Y k ≠ z:=by
     intro k hk
     rcases lt_or_eq_of_le hk with hk|hk
     · exact hnov k hk
     · subst k
       rw [hclY]
       exact hnov 0 (by omega)
   have hallj:∀j ∈ Finset.range n,
       ∀ᶠ t in nhds z,
         PT X Y e j t = PT X Y e j z:=by
     intro j hj
     have hjn:j < n:=Finset.mem_range.mp hj
     have h0:=hnov j hjn
     have h1:=hnov' (j+1) (by omega)
     apply prefTerm_eventually_of_noend X Y h0 h1
     rcases eq_or_ne j e with rfl | hje
     · exact Or.inl rfl
     · refine Or.inr ?_
       intro hja
       exact hopenne hjn he hje hja hzact
   have halla:∀ᶠ t in nhds z,∀j ∈ Finset.range n,
         PT X Y e j t = PT X Y e j z :=
     (Finset.eventually_all (Finset.range n)).2 hallj
   filter_upwards [halla] with t ht
   unfold pref
   exact Finset.sum_congr rfl (by
     intro j hj
     exact ht j hj)
 have at_vertex (k:ℕ) (hk:k < n)
     (hz:( (Y k):ℝ) ∈ I) :
     ∀ᶠ t in nhds (Y k),
       pref X Y n e t = pref X Y n e (Y k):=by
   have hn0:0 < n:=by omega
   let p:ℕ:=if k = 0 then n-1 else k-1
   have hp:p < n:=by
     dsimp [p]; split_ifs <;> omega
   have hpk:p + 1 = k ∨ (k = 0 ∧ p+1 = n):=by
     dsimp [p]
     by_cases h:k = 0
     · simp [h,Nat.sub_add_cancel (by omega:1 ≤ n)]
     · left; simp [h]; omega
   have hYpk:Y (p+1) = Y k:=by
     rcases hpk with hpk | hpk
     · rw [hpk]
     · rw [hpk.2,hclY,hpk.1]
   have hXpk:X (p+1) = X k:=by
     rcases hpk with hpk | hpk
     · rw [hpk]
     · rw [hpk.2,hclX,hpk.1]
   have hpkne:p ≠ k:=by
     dsimp [p]
     by_cases h:k = 0
     · simp [h]; omega
     · simp [h]; omega
   have hpek':k ≠ e:=by
     intro hke
     subst k
     have zz:¬ (Y e ∈ I):=by
       dsimp [I]
       rcases le_total (Y e) (Y (e+1)) with h|h <;>
         simp [min_eq_left,min_eq_right,max_eq_left,max_eq_right,h]
     exact zz hz
   have hpe:p ≠ e:=by
     intro hh
     have hhY:Y (e+1) = Y k:=by rw [← hh]; exact hYpk
     have zz:¬ (Y (e+1) ∈ I):=by
       dsimp [I]
       rcases le_total (Y e) (Y (e+1)) with h|h <;>
         simp [min_eq_left,min_eq_right,max_eq_left,max_eq_right,h]
     rw [hhY] at zz
     exact zz hz
   have hpak:Y p ≠ Y k:=hdiff p hp k hk hpkne
   have hknext:Y (k+1) ≠ Y k:=hside k hk
   have heact:SA Y e (Y k):=hact ⟨Y k,hz⟩
   have hxne:X k ≠ SX X Y e (Y k) :=
     (hvert he hk (Ne.symm hpek') heact).symm
   have hpair:=incident_terms_eventually X Y (e:=e) (p:=p) (k:=k)
       hYpk hXpk hpak hknext hxne
   have other:∀j ∈ Finset.range n,j ≠ p → j ≠ k → ∀ᶠ t in nhds (Y k),
            PT X Y e j t = PT X Y e j (Y k):=by
     intro j hj hjp hjk
     have hjn:j < n:=Finset.mem_range.mp hj
     have h0:Y j ≠ Y k:=hdiff j hjn k hk hjk
     have h1:Y (j+1) ≠ Y k:=by
       have hjle:j+1 ≤ n:=by omega
       rcases lt_or_eq_of_le hjle with hl|hl
       · have hne:j+1 ≠ k:=by
           intro hh
           have hjeqp:j = p:=by
             rcases hpk with hpk|hpk
             · omega
             · have hkzero:k = 0:=hpk.1
               omega
           exact hjp hjeqp
         exact hdiff (j+1) hl k hk hne
       · have hk0:k ≠ 0:=by
           intro hh
           subst k
           have hh':j = p:=by
             have hjval:j = n-1:=by omega
             dsimp [p]
             simp [hjval]
           exact hjp hh'
         rw [hl,hclY]
         exact hdiff 0 (by omega) k hk (Ne.symm hk0)
     apply prefTerm_eventually_of_noend X Y h0 h1
     rcases eq_or_ne j e with hje|hje
     · exact Or.inl hje
     · refine Or.inr ?_
       intro hja
       exact hopenne hjn he hje hja heact
   have othall:∀ᶠ t in nhds (Y k),∀j ∈ Finset.range n,
       j ≠ p → j ≠ k → PT X Y e j t = PT X Y e j (Y k):=by
     apply (Finset.eventually_all (Finset.range n)).2
     intro j hj
     by_cases hjp:j = p
     · filter_upwards [] with t
       intro hne _; exact (hne hjp).elim
     · by_cases hjk:j = k
       · filter_upwards [] with t
         intro _ hne; exact (hne hjk).elim
       · have H:=other j hj hjp hjk
         filter_upwards [H] with t ht
         intro _ _
         exact ht
   filter_upwards [hpair,othall] with t ht hoth
   unfold pref
   have hp_mem:p ∈ Finset.range n:=Finset.mem_range.mpr hp
   have hk_mem:k ∈ Finset.range n:=Finset.mem_range.mpr hk
   calc
     (∑ j ∈ Finset.range n,PT X Y e j t) =
         (∑ j ∈ (Finset.range n).erase p |>.erase k,
               PT X Y e j t) +
           PT X Y e p t + PT X Y e k t:=by
             have hnepk:k ≠ p:=Ne.symm hpkne
             rw [show Finset.range n =
                 insert p (insert k ((Finset.range n).erase p |>.erase k)) by
                   ext a
                   by_cases ha:a = p
                   · subst a; simp [hp_mem]
                   · by_cases ha':a = k
                     · subst a; simp [hk_mem,hnepk]
                     · simp [ha,ha']]
             simp [hpkne,add_assoc,add_left_comm,add_comm]
     _ = (∑ j ∈ (Finset.range n).erase p |>.erase k,
               PT X Y e j (Y k)) +
           PT X Y e p (Y k) + PT X Y e k (Y k):=by
             have heqsum:(∑ j ∈ (Finset.range n).erase p |>.erase k,
                   PT X Y e j t) =
                   ∑ j ∈ (Finset.range n).erase p |>.erase k,
                   PT X Y e j (Y k):=by
               apply Finset.sum_congr rfl
               intro j hj
               have hmem:j ∈ Finset.range n:=by
                 have h:=Finset.mem_of_subset (Finset.erase_subset _ _) hj
                 exact Finset.mem_of_subset (Finset.erase_subset _ _) h
               have hjk:j ≠ k:=by
                 exact (Finset.mem_erase.mp hj).1
               have hjp:j ≠ p:=by
                 have hhj:j ∈ (Finset.range n).erase p :=
                   Finset.mem_of_subset (Finset.erase_subset _ _) hj
                 exact (Finset.mem_erase.mp hhj).1
               exact hoth j hmem hjp hjk
             rw [heqsum]
             omega
     _ = (∑ j ∈ Finset.range n,PT X Y e j (Y k)):=by
             rw [show Finset.range n =
                 insert p (insert k ((Finset.range n).erase p |>.erase k)) by
                   ext a
                   by_cases ha:a = p
                   · subst a; simp [hp_mem]
                   · by_cases ha':a = k
                     · subst a; simp [hk_mem,Ne.symm hpkne]
                     · simp [ha,ha']]
             simp [hpkne,add_assoc,add_left_comm,add_comm]
 have hlocal:IsLocallyConstant (fun z:I => pref X Y n e (z:ℝ)):=by
   apply (IsLocallyConstant.iff_eventually_eq _).2
   intro z
   by_cases hv:∃k,k < n ∧ Y k = (z:ℝ)
   · rcases hv with ⟨k,hk,hkz⟩
     have hzv:( (Y k):ℝ) ∈ I:=by simpa [hkz] using z.property
     have H:=at_vertex k hk hzv
     have H':=(continuousAt_subtype_val (x:=z)).eventually
         (by simpa [hkz] using H)
     exact H'
   · have hn:∀k,k < n → Y k ≠ (z:ℝ):=by
       intro k hk h; exact hv ⟨k,hk,h⟩
     have H:=novtx (z:ℝ) (hact z) hn
     exact (continuousAt_subtype_val (x:=z)).eventually H
 let zm:I:=⟨_,mid_mem _ _ (Ne.symm hne_e)⟩
 let zu:I:=⟨u,huI⟩
 letI:PreconnectedSpace I:=Subtype.preconnectedSpace (isPreconnected_Ioo)
 have hEq:=hlocal.apply_eq_of_preconnectedSpace zu zm
 simpa [EP,zu,zm] using hEq
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/CyclePrefix.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/InitialPrefix.lean
set_option linter.all false
namespace H
open scoped BigOperators
open Filter Set Topology Classical
lemma edgePref_zero_first_of_support
   (X Y:ℕ → ℝ) (n:ℕ) (hn:3 ≤ n)
   (hclX:X n = X 0) (hclY:Y n = Y 0)
   (hX0:X 0 = 0) (hY0:Y 0 = 0)
   (hY1:0 < Y 1) (hYp:Y (n-1) < 0)
   (hXall:∀i ≤ n,0 ≤ X i)
   (hdiff:∀i,i < n → ∀j,j < n → i ≠ j → Y i ≠ Y j)
   (hside:∀j,j < n → Y (j+1) ≠ Y j)
   (hopenne:∀{a b:ℕ},a < n → b < n → a ≠ b → ∀{u:ℝ},SA Y a u → SA Y b u → SX X Y a u ≠ SX X Y b u)
   (hvert:∀{a k:ℕ},a < n → k < n → a ≠ k → SA Y a (Y k) → SX X Y a (Y k) ≠ X k) :
   EP X Y n 0 = 0:=by
 classical
 have hn0:0 < n:=by omega
 have hp_lt:n-1 < n:=by omega
 have hp_ne0:n-1 ≠ 0:=by omega
 have hxsl:∀{j:ℕ},j < n → ∀{u:ℝ},
       SA Y j u → 0 ≤ SX X Y j u:=by
   intro j hj u hu
   have ht:=param_pos_lt_one hu
   dsimp [SX]
   have A:0 ≤ (1 - SP Y j u) * X j :=
     mul_nonneg (by linarith) (hXall j (by omega))
   have B:0 ≤ (SP Y j u) * X (j+1) :=
     mul_nonneg ht.1.le (hXall (j+1) (by omega))
   linarith
 have hside0:Y (0+1) ≠ Y 0:=hside 0 (by omega)
 have hxref:SX X Y 0 (0:ℝ) = 0:=by
   have hh:=(sliceX_start (X:=X) (Y:=Y) hside0)
   simpa [hY0,hX0] using hh
 have hother:∀j ∈ Finset.range n,j ≠ 0 → j ≠ n-1 → ∀ᶠ u in nhds (0:ℝ),PT X Y 0 j u = 0:=by
   intro j hj hj0 hjpne
   have hjlt:j < n:=Finset.mem_range.mp hj
   have hj1lt:j+1 < n:=by omega
   have h0v:Y j ≠ (0:ℝ):=by
     have h:=hdiff j hjlt 0 hn0 hj0
     simpa [hY0] using h
   have h1v:Y (j+1) ≠ (0:ℝ):=by
     have h:=hdiff (j+1) hj1lt 0 hn0 (by omega)
     simpa [hY0] using h
   have hxvert:SA Y j (0:ℝ) → SX X Y j (0:ℝ) ≠ SX X Y 0 (0:ℝ):=by
     intro ha
     have hh:=hvert (a:=j) (k:=0) hjlt hn0 hj0
         (by simpa [hY0] using ha)
     simpa [hY0,hxref,hX0] using hh
   have hval:PT X Y 0 j (0:ℝ) = 0:=by
     by_cases hx:SX X Y j (0:ℝ) < SX X Y 0 (0:ℝ)
     · have hxneg:SX X Y j (0:ℝ) < 0:=by simpa [hxref] using hx
       have hu':¬ (Y j ≤ (0:ℝ) ∧ (0:ℝ) < Y (j+1)):=by
         intro hu
         have ha:SA Y j (0:ℝ) :=
           Or.inl ⟨lt_of_le_of_ne hu.1 h0v,hu.2⟩
         have hnn:=hxsl hjlt ha
         linarith
       have hd':¬ (Y (j+1) ≤ (0:ℝ) ∧ (0:ℝ) < Y j):=by
         intro hd
         have ha:SA Y j (0:ℝ) :=
           Or.inr ⟨lt_of_le_of_ne hd.1 h1v,hd.2⟩
         have hnn:=hxsl hjlt ha
         linarith
       simp [PT,hx,hu',hd']
     · simp [PT,hx]
   have He:=prefTerm_eventually_of_noend X Y (e:=0) (j:=j)
         (z:=(0:ℝ)) h0v h1v (Or.inr hxvert)
   filter_upwards [He] with u hu
   simpa [hval] using hu
 have hall:∀ᶠ u in nhds (0:ℝ),
       ∀j ∈ Finset.range n,j ≠ 0 → j ≠ n-1 → PT X Y 0 j u = 0:=by
   apply (Finset.eventually_all (Finset.range n)).2
   intro j hj
   by_cases hj0:j = 0
   · filter_upwards [] with u
     intro hh
     exact (hh hj0).elim
   · by_cases hjp0:j = n-1
     · filter_upwards [] with u
       intro _ hh
       exact (hh hjp0).elim
     · have H:=hother j hj hj0 hjp0
       filter_upwards [H] with u hu
       intro _ _
       exact hu
 rcases (Metric.mem_nhds_iff.mp hall) with ⟨ε,hε,hεsub⟩
 let u:ℝ:=min (ε/2) (Y 1 / 2)
 have hu0:0 < u:=by
   dsimp [u]
   exact lt_min (by linarith) (by linarith)
 have hu1:u < Y 1:=by
   have h:=min_le_right (ε/2) (Y 1 / 2)
   dsimp [u]
   linarith
 have hue:u < ε:=by
   have h:=min_le_left (ε/2) (Y 1 / 2)
   dsimp [u]
   linarith
 have hu_ball:u ∈ Metric.ball (0:ℝ) ε:=by
   rw [Metric.mem_ball]
   rw [dist_zero_right]
   rw [Real.norm_eq_abs,abs_of_pos hu0]
   exact hue
 have hallu:=hεsub hu_ball
 have hp_end:n-1+1 = n:=by omega
 have hYend:Y (n-1+1) = 0:=by rw [hp_end,hclY,hY0]
 have hpterm:PT X Y 0 (n-1) u = 0:=by
   have ha:¬ (Y (n-1) ≤ u ∧ u < Y (n-1+1)):=by
     rw [hYend]
     intro h; linarith
   have hb:¬ (Y (n-1+1) ≤ u ∧ u < Y (n-1)):=by
     rw [hYend]
     intro h; linarith
   by_cases hxx:SX X Y (n-1) u < SX X Y 0 u <;>
     simp [PT,hxx,ha,hb]
 have hsum0:pref X Y n 0 u = 0:=by
   unfold pref
   have hallterms:∀j ∈ Finset.range n,PT X Y 0 j u = 0:=by
     intro j hj
     rcases eq_or_ne j 0 with h|h
     · subst j
       simp [PT]
     · rcases eq_or_ne j (n-1) with h'|h'
       · subst j; exact hpterm
       · exact hallu j hj h h'
   calc
     (∑ j ∈ Finset.range n,PT X Y 0 j u) =
         ∑ j ∈ Finset.range n,(0:ℤ):=by
           apply Finset.sum_congr rfl
           intro j hj
           exact hallterms j hj
     _ = 0:=by simp
 have hact0:SA Y 0 u:=by
   left
   simpa [hY0] using (show (0:ℝ) < u ∧ u < Y 1 from ⟨hu0,hu1⟩)
 have hconst:=edgePref_eq X Y n hn hclX hclY hdiff hside
      hopenne hvert (e:=0) (u:=u) (by omega) hact0
 rw [hsum0] at hconst
 exact hconst.symm
lemma edgePref_zero_last_of_support
   (X Y:ℕ → ℝ) (n:ℕ) (hn:3 ≤ n)
   (hclX:X n = X 0) (hclY:Y n = Y 0)
   (hX0:X 0 = 0) (hY0:Y 0 = 0)
   (hY1:0 < Y 1) (hYp:Y (n-1) < 0)
   (hXall:∀i ≤ n,0 ≤ X i)
   (hdiff:∀i,i < n → ∀j,j < n → i ≠ j → Y i ≠ Y j)
   (hside:∀j,j < n → Y (j+1) ≠ Y j)
   (hopenne:∀{a b:ℕ},a < n → b < n → a ≠ b → ∀{u:ℝ},SA Y a u → SA Y b u → SX X Y a u ≠ SX X Y b u)
   (hvert:∀{a k:ℕ},a < n → k < n → a ≠ k → SA Y a (Y k) → SX X Y a (Y k) ≠ X k) :
   EP X Y n (n-1) = 0:=by
 classical
 have hn0:0 < n:=by omega
 have hp_lt:n-1 < n:=by omega
 have hp_ne0:n-1 ≠ 0:=by omega
 have hpnext:n-1+1 = n:=by omega
 have hxsl:∀{j:ℕ},j < n → ∀{u:ℝ},
       SA Y j u → 0 ≤ SX X Y j u:=by
   intro j hj u hu
   have ht:=param_pos_lt_one hu
   dsimp [SX]
   have A:0 ≤ (1 - SP Y j u) * X j :=
     mul_nonneg (by linarith) (hXall j (by omega))
   have B:0 ≤ (SP Y j u) * X (j+1) :=
     mul_nonneg ht.1.le (hXall (j+1) (by omega))
   linarith
 have hpend:Y (n-1+1) ≠ Y (n-1):=hside (n-1) hp_lt
 have hxref:SX X Y (n-1) (0:ℝ) = 0:=by
   have hh:=(sliceX_end (X:=X) (Y:=Y) hpend)
   rw [hpnext,hclY,hY0] at hh
   simpa [hpnext,hclX,hX0] using hh
 have hother:∀j ∈ Finset.range n,j ≠ 0 → j ≠ n-1 → ∀ᶠ u in nhds (0:ℝ),PT X Y (n-1) j u = 0:=by
   intro j hj hj0 hjpne
   have hjlt:j < n:=Finset.mem_range.mp hj
   have hj1lt:j+1 < n:=by omega
   have h0v:Y j ≠ (0:ℝ):=by
     have h:=hdiff j hjlt 0 hn0 hj0
     simpa [hY0] using h
   have h1v:Y (j+1) ≠ (0:ℝ):=by
     have h:=hdiff (j+1) hj1lt 0 hn0 (by omega)
     simpa [hY0] using h
   have hxvert:SA Y j (0:ℝ) → SX X Y j (0:ℝ) ≠ SX X Y (n-1) (0:ℝ):=by
     intro ha
     have hh:=hvert (a:=j) (k:=0) hjlt hn0 hj0
         (by simpa [hY0] using ha)
     simpa [hY0,hxref,hX0] using hh
   have hval:PT X Y (n-1) j (0:ℝ) = 0:=by
     by_cases hx:SX X Y j (0:ℝ) <
           SX X Y (n-1) (0:ℝ)
     · have hxneg:SX X Y j (0:ℝ) < 0:=by simpa [hxref] using hx
       have hu':¬ (Y j ≤ (0:ℝ) ∧ (0:ℝ) < Y (j+1)):=by
         intro hu
         have ha:SA Y j (0:ℝ) :=
           Or.inl ⟨lt_of_le_of_ne hu.1 h0v,hu.2⟩
         have hnn:=hxsl hjlt ha
         linarith
       have hd':¬ (Y (j+1) ≤ (0:ℝ) ∧ (0:ℝ) < Y j):=by
         intro hd
         have ha:SA Y j (0:ℝ) :=
           Or.inr ⟨lt_of_le_of_ne hd.1 h1v,hd.2⟩
         have hnn:=hxsl hjlt ha
         linarith
       simp [PT,hx,hu',hd']
     · simp [PT,hx]
   have He:=prefTerm_eventually_of_noend X Y (e:=(n-1)) (j:=j)
         (z:=(0:ℝ)) h0v h1v (Or.inr hxvert)
   filter_upwards [He] with u hu
   simpa [hval] using hu
 have hall:∀ᶠ u in nhds (0:ℝ),
       ∀j ∈ Finset.range n,j ≠ 0 → j ≠ n-1 → PT X Y (n-1) j u = 0:=by
   apply (Finset.eventually_all (Finset.range n)).2
   intro j hj
   by_cases hj0:j = 0
   · filter_upwards [] with u
     intro hh
     exact (hh hj0).elim
   · by_cases hjp0:j = n-1
     · filter_upwards [] with u
       intro _ hh
       exact (hh hjp0).elim
     · have H:=hother j hj hj0 hjp0
       filter_upwards [H] with u hu
       intro _ _
       exact hu
 rcases (Metric.mem_nhds_iff.mp hall) with ⟨ε,hε,hεsub⟩
 let t:ℝ:=min (ε/2) ((- Y (n-1))/2)
 let u:ℝ:=-t
 have ht0:0 < t:=by
   dsimp [t]
   exact lt_min (by linarith) (by linarith)
 have hu0:u < 0:=by dsimp [u]; linarith
 have htY:t < - Y (n-1):=by
   have h:=min_le_right (ε/2) ((- Y (n-1))/2)
   dsimp [t]
   linarith
 have hYpu:Y (n-1) < u:=by dsimp [u]; linarith
 have hte:t < ε:=by
   have h:=min_le_left (ε/2) ((- Y (n-1))/2)
   dsimp [t]
   linarith
 have hu_ball:u ∈ Metric.ball (0:ℝ) ε:=by
   rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs]
   have:|u| = t:=by dsimp [u]; simp [abs_of_pos ht0]
   rw [this]
   exact hte
 have hallu:=hεsub hu_ball
 have hzfirst:PT X Y (n-1) 0 u = 0:=by
   have hden:Y (0+1) ≠ Y 0:=hside 0 (by omega)
   have ha:¬ (Y 0 ≤ u ∧ u < Y (0+1)):=by
     rw [hY0]
     intro h; linarith
   have hb:¬ (Y (0+1) ≤ u ∧ u < Y 0):=by
     rw [hY0]
     intro h; linarith [hY1]
   by_cases hxx:SX X Y 0 u < SX X Y (n-1) u <;>
     simp [PT,hxx,ha,hb]
 have hsum0:pref X Y n (n-1) u = 0:=by
   unfold pref
   have allterms:∀j ∈ Finset.range n,
         PT X Y (n-1) j u = 0:=by
     intro j hj
     rcases eq_or_ne j 0 with h|h
     · subst j; exact hzfirst
     · rcases eq_or_ne j (n-1) with h'|h'
       · subst j; simp [PT]
       · exact hallu j hj h h'
   calc
     (∑ j ∈ Finset.range n,PT X Y (n-1) j u) =
         ∑ j ∈ Finset.range n,(0:ℤ):=by
           apply Finset.sum_congr rfl
           intro j hj
           exact allterms j hj
     _ = 0:=by simp
 have hact:SA Y (n-1) u:=by
   left
   rw [hpnext,hclY,hY0]
   exact ⟨hYpu,hu0⟩
 have hconst:=edgePref_eq X Y n hn hclX hclY hdiff hside
      hopenne hvert (e:=(n-1)) (u:=u) hp_lt hact
 rw [hsum0] at hconst
 exact hconst.symm
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/InitialPrefix.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Propagation.lean
set_option linter.all false
namespace H
open scoped BigOperators
open Filter Set Topology
open Classical
lemma edgePref_next_inner
   (X Y:ℕ → ℝ) (n k:ℕ) (hn:3 ≤ n)
   (hclX:X n = X 0) (hclY:Y n = Y 0)
   (hdiff:∀i,i < n → ∀j,j < n → i ≠ j → Y i ≠ Y j)
   (hside:∀j,j < n → Y (j+1) ≠ Y j)
   (hopenne:∀{a b:ℕ},a < n → b < n → a ≠ b → ∀{u:ℝ},SA Y a u → SA Y b u → SX X Y a u ≠ SX X Y b u)
   (hvert:∀{a t:ℕ},a < n → t < n → a ≠ t → SA Y a (Y t) → SX X Y a (Y t) ≠ X t)
   (hk0:0 < k) (hk1:k + 1 < n) :
   (Y (k-1) < Y k ∧ Y k < Y (k+1) → EP X Y n k = EP X Y n (k-1)) ∧
   (Y k < Y (k-1) ∧ Y (k+1) < Y k → EP X Y n k = EP X Y n (k-1)) ∧
   (Y (k-1) < Y k ∧ Y (k+1) < Y k → EP X Y n k = EP X Y n (k-1) + 1) ∧
   (Y k < Y (k-1) ∧ Y k < Y (k+1) → EP X Y n k = EP X Y n (k-1) - 1):=by
 classical
 let p:ℕ:=k-1
 have hp_lt:p < n:=by dsimp [p]; omega
 have hk_lt:k < n:=by omega
 have hp1:p + 1 = k:=by dsimp [p]; omega
 have hpk:p ≠ k:=by dsimp [p]; omega
 have hp_mem:p ∈ Finset.range n:=Finset.mem_range.mpr hp_lt
 have hk_mem:k ∈ Finset.range n:=Finset.mem_range.mpr hk_lt
 have hpden:Y (p+1) ≠ Y p:=hside p hp_lt
 have hkden:Y (k+1) ≠ Y k:=hside k hk_lt
 have hxp:SX X Y p (Y k) = X k:=by
   rw [← hp1,sliceX_end hpden,hp1]
 have hxk:SX X Y k (Y k) = X k:=by
   rw [sliceX_start hkden]
 have hother:∀j ∈ Finset.range n,j ≠ p → j ≠ k → ∀ᶠ u in nhds (Y k),
         PT X Y p j u = PT X Y p j (Y k) ∧
         PT X Y k j u = PT X Y p j (Y k):=by
   intro j hj hjp hjk
   have hjlt:j < n:=Finset.mem_range.mp hj
   have h0:Y j ≠ Y k:=hdiff j hjlt k hk_lt hjk
   have h1:Y (j+1) ≠ Y k:=by
     have hjle:j+1 ≤ n:=by omega
     rcases lt_or_eq_of_le hjle with hlt | heq
     · have hnek:j+1 ≠ k:=by
         intro hh
         have:j = p:=by omega
         exact hjp this
       exact hdiff (j+1) hlt k hk_lt hnek
     · have hkz:k ≠ 0:=Nat.ne_of_gt hk0
       rw [heq,hclY]
       exact hdiff 0 (by omega) k hk_lt (Ne.symm hkz)
   have hnep:(SA Y j (Y k) → SX X Y j (Y k) ≠ SX X Y p (Y k)):=by
     intro ha
     have hh:=hvert (a:=j) (t:=k) hjlt hk_lt hjk ha
     simpa [hxp] using hh
   have hnek:(SA Y j (Y k) → SX X Y j (Y k) ≠ SX X Y k (Y k)):=by
     intro ha
     have hh:=hvert (a:=j) (t:=k) hjlt hk_lt hjk ha
     simpa [hxk] using hh
   have ep:=prefTerm_eventually_of_noend X Y (e:=p) (j:=j)
         h0 h1 (Or.inr hnep)
   have ek:=prefTerm_eventually_of_noend X Y (e:=k) (j:=j)
         h0 h1 (Or.inr hnek)
   have heqv:PT X Y k j (Y k) = PT X Y p j (Y k):=by
     unfold PT
     rw [hxp,hxk]
   filter_upwards [ep,ek] with u hu hv
   exact ⟨hu,hv.trans heqv⟩
 have hall:∀ᶠ u in nhds (Y k),∀j ∈ Finset.range n,j ≠ p → j ≠ k → PT X Y p j u = PT X Y p j (Y k) ∧
         PT X Y k j u = PT X Y p j (Y k):=by
   apply (Finset.eventually_all (Finset.range n)).2
   intro j hj
   by_cases hjp:j = p
   · filter_upwards [] with u
     intro h
     exact (h hjp).elim
   · by_cases hjk:j = k
     · filter_upwards [] with u
       intro _ h
       exact (h hjk).elim
     · have H:=hother j hj hjp hjk
       filter_upwards [H] with u hu
       intro _ _
       exact hu
 rcases (Metric.mem_nhds_iff.mp hall) with ⟨ε,hε,hεsub⟩
 let S:ℤ:=∑ j ∈ (Finset.range n).erase p |>.erase k,
                 PT X Y p j (Y k)
 have sumdecomp (e:ℕ) (u:ℝ) :
     pref X Y n e u =
       (∑ j ∈ (Finset.range n).erase p |>.erase k,
            PT X Y e j u) +
         PT X Y e p u + PT X Y e k u:=by
   unfold pref
   rw [show Finset.range n =
         insert p (insert k ((Finset.range n).erase p |>.erase k)) by
     ext a
     by_cases ha:a = p
     · subst a; simp [hp_mem]
     · by_cases hb:a = k
       · subst a; simp [hk_mem,Ne.symm hpk]
       · simp [ha,hb]]
   simp [hpk,add_assoc,add_left_comm,add_comm]
 have sumat (u:ℝ) (hu:u ∈ Metric.ball (Y k) ε) :
     (∑ j ∈ (Finset.range n).erase p |>.erase k,
          PT X Y p j u) = S ∧
     (∑ j ∈ (Finset.range n).erase p |>.erase k,
          PT X Y k j u) = S:=by
   have hz:=hεsub hu
   dsimp [S]
   constructor
   · apply Finset.sum_congr rfl
     intro j hj
     have hmem1:j ∈ (Finset.range n).erase p :=
       Finset.mem_of_subset (Finset.erase_subset _ _) hj
     have hmem:j ∈ Finset.range n :=
       Finset.mem_of_subset (Finset.erase_subset _ _) hmem1
     have hneK:j ≠ k:=(Finset.mem_erase.mp hj).1
     have hneP:j ≠ p:=(Finset.mem_erase.mp hmem1).1
     exact (hz j hmem hneP hneK).1
   · apply Finset.sum_congr rfl
     intro j hj
     have hmem1:j ∈ (Finset.range n).erase p :=
       Finset.mem_of_subset (Finset.erase_subset _ _) hj
     have hmem:j ∈ Finset.range n :=
       Finset.mem_of_subset (Finset.erase_subset _ _) hmem1
     have hneK:j ≠ k:=(Finset.mem_erase.mp hj).1
     have hneP:j ≠ p:=(Finset.mem_erase.mp hmem1).1
     exact (hz j hmem hneP hneK).2
 have below (L:ℝ) (hL:L < Y k) :
     ∃u:ℝ,u ∈ Metric.ball (Y k) ε ∧ L < u ∧ u < Y k:=by
   let δ:ℝ:=min (ε/2) ((Y k - L)/2)
   have hδ:0 < δ:=lt_min (by linarith) (by linarith)
   have hδε:δ < ε:=by
     have hh:=min_le_left (ε/2) ((Y k - L)/2)
     dsimp [δ]
     linarith
   have hδL:δ < Y k - L:=by
     have hh:=min_le_right (ε/2) ((Y k - L)/2)
     dsimp [δ]
     linarith
   refine ⟨Y k - δ,?_,?_,?_⟩
   · rw [Metric.mem_ball,Real.dist_eq]
     rw [abs_of_nonpos (by linarith:Y k - δ - Y k ≤ 0)]
     linarith
   · linarith
   · linarith
 have above (L:ℝ) (hL:Y k < L) :
     ∃u:ℝ,u ∈ Metric.ball (Y k) ε ∧ Y k < u ∧ u < L:=by
   let δ:ℝ:=min (ε/2) ((L - Y k)/2)
   have hδ:0 < δ:=lt_min (by linarith) (by linarith)
   have hδε:δ < ε:=by
     have hh:=min_le_left (ε/2) ((L - Y k)/2)
     dsimp [δ]
     linarith
   have hδL:δ < L - Y k:=by
     have hh:=min_le_right (ε/2) ((L - Y k)/2)
     dsimp [δ]
     linarith
   refine ⟨Y k + δ,?_,?_,?_⟩
   · rw [Metric.mem_ball,Real.dist_eq]
     rw [abs_of_nonneg (by linarith:0 ≤ Y k + δ - Y k)]
     linarith
   · linarith
   · linarith
 have selfzero (e:ℕ) (u:ℝ):PT X Y e e u = 0:=by
   simp [PT]
 constructor
 · intro hmono
   have hyp:Y p < Y k:=by simpa [p] using hmono.1
   have hyn:Y k < Y (k+1):=hmono.2
   obtain ⟨u,huB,huL,huz⟩:=below (Y p) hyp
   obtain ⟨v0,hvB,hvz,hvU⟩:=above (Y (k+1)) hyn
   have hpu:SA Y p u:=Or.inl ⟨huL,by simpa [hp1] using huz⟩
   have hkv:SA Y k v0:=Or.inl ⟨hvz,hvU⟩
   have hpk_u:PT X Y p k u = 0:=by
     have n1:¬ (Y k ≤ u ∧ u < Y (k+1)):=by intro h; linarith
     have n2:¬ (Y (k+1) ≤ u ∧ u < Y k):=by intro h; linarith
     by_cases hx:SX X Y k u < SX X Y p u <;>
       simp [PT,hx,n1,n2]
   have hkp_v:PT X Y k p v0 = 0:=by
     have n1:¬ (Y p ≤ v0 ∧ v0 < Y (p+1)):=by rw [hp1]; intro h; linarith
     have n2:¬ (Y (p+1) ≤ v0 ∧ v0 < Y p):=by rw [hp1]; intro h; linarith
     by_cases hx:SX X Y p v0 < SX X Y k v0 <;>
       simp [PT,hx,n1,n2]
   have Dp:=sumdecomp p u
   have Dk:=sumdecomp k v0
   have Sp:=(sumat u huB).1
   have Sk:=(sumat v0 hvB).2
   have Cp:=edgePref_eq X Y n hn hclX hclY hdiff hside hopenne hvert
         (e:=p) hp_lt hpu
   have Ck:=edgePref_eq X Y n hn hclX hclY hdiff hside hopenne hvert
         (e:=k) hk_lt hkv
   have Ep:EP X Y n p = S:=by
     rw [sumdecomp p u,Sp,selfzero,hpk_u] at Cp
     linarith
   have Ek:EP X Y n k = S:=by
     rw [sumdecomp k v0,Sk,selfzero,hkp_v] at Ck
     linarith
   simpa [p,Ep] using (Ek.trans Ep.symm)
 · constructor
   · intro hmono
     have hyp:Y k < Y p:=by simpa [p] using hmono.1
     have hyn:Y (k+1) < Y k:=hmono.2
     obtain ⟨u,huB,huz,huU⟩:=above (Y p) hyp
     obtain ⟨v0,hvB,hvL,hvz⟩:=below (Y (k+1)) hyn
     have hpu:SA Y p u:=Or.inr ⟨by simpa [hp1] using huz,huU⟩
     have hkv:SA Y k v0:=Or.inr ⟨hvL,hvz⟩
     have hpk_u:PT X Y p k u = 0:=by
       have n1:¬ (Y k ≤ u ∧ u < Y (k+1)):=by intro h; linarith
       have n2:¬ (Y (k+1) ≤ u ∧ u < Y k):=by intro h; linarith
       by_cases hx:SX X Y k u < SX X Y p u <;>
         simp [PT,hx,n1,n2]
     have hkp_v:PT X Y k p v0 = 0:=by
       have n1:¬ (Y p ≤ v0 ∧ v0 < Y (p+1)):=by rw [hp1]; intro h; linarith
       have n2:¬ (Y (p+1) ≤ v0 ∧ v0 < Y p):=by rw [hp1]; intro h; linarith
       by_cases hx:SX X Y p v0 < SX X Y k v0 <;>
         simp [PT,hx,n1,n2]
     have Cp:=edgePref_eq X Y n hn hclX hclY hdiff hside hopenne hvert
         (e:=p) hp_lt hpu
     have Ck:=edgePref_eq X Y n hn hclX hclY hdiff hside hopenne hvert
         (e:=k) hk_lt hkv
     rw [sumdecomp p u,(sumat u huB).1,selfzero,hpk_u] at Cp
     rw [sumdecomp k v0,(sumat v0 hvB).2,selfzero,hkp_v] at Ck
     simpa [p] using (Ck.symm.trans Cp)
   · constructor
     · intro hmax
       have hyp:Y p < Y k:=by simpa [p] using hmax.1
       have hyn:Y (k+1) < Y k:=hmax.2
       obtain ⟨u,huB,huL,huZ⟩:=below (max (Y p) (Y (k+1))) (by
           exact max_lt hyp hyn)
       have hup:Y p < u:=lt_of_le_of_lt (le_max_left _ _) huL
       have hun:Y (k+1) < u:=lt_of_le_of_lt (le_max_right _ _) huL
       have hpa:SA Y p u:=Or.inl ⟨hup,by simpa [hp1] using huZ⟩
       have hka:SA Y k u:=Or.inr ⟨hun,huZ⟩
       have hnepk:SX X Y p u ≠ SX X Y k u :=
         hopenne hp_lt hk_lt hpk hpa hka
       have Cp:=edgePref_eq X Y n hn hclX hclY hdiff hside hopenne hvert
         (e:=p) hp_lt hpa
       have Ck:=edgePref_eq X Y n hn hclX hclY hdiff hside hopenne hvert
         (e:=k) hk_lt hka
       rcases lt_or_gt_of_ne hnepk with hlt | hgt
       · have tpk:PT X Y p k u = 0:=by
           have hx:¬ SX X Y k u < SX X Y p u:=not_lt_of_ge hlt.le
           simp [PT,hx]
         have tkp:PT X Y k p u = 1:=by
           have up:Y p ≤ u ∧ u < Y (p+1):=⟨hup.le,by simpa [hp1] using huZ⟩
           have dn:¬ (Y (p+1) ≤ u ∧ u < Y p):=by rw [hp1]; intro h; linarith
           simp [PT,hlt,up,dn]
         rw [sumdecomp p u,(sumat u huB).1,selfzero,tpk] at Cp
         rw [sumdecomp k u,(sumat u huB).2,selfzero,tkp] at Ck
         simpa [p] using (show EP X Y n k = EP X Y n p + 1 by linarith [Cp,Ck])
       · have tpk:PT X Y p k u = -1:=by
           have dn:Y (k+1) ≤ u ∧ u < Y k:=⟨hun.le,huZ⟩
           have un:¬ (Y k ≤ u ∧ u < Y (k+1)):=by intro h; linarith
           simp [PT,hgt,dn,un]
         have tkp:PT X Y k p u = 0:=by
           have hx:¬ SX X Y p u < SX X Y k u:=not_lt_of_ge hgt.le
           simp [PT,hx]
         rw [sumdecomp p u,(sumat u huB).1,selfzero,tpk] at Cp
         rw [sumdecomp k u,(sumat u huB).2,selfzero,tkp] at Ck
         simpa [p] using (show EP X Y n k = EP X Y n p + 1 by linarith [Cp,Ck])
     · intro hmin
       have hyp:Y k < Y p:=by simpa [p] using hmin.1
       have hyn:Y k < Y (k+1):=hmin.2
       obtain ⟨u,huB,huZ,huL⟩:=above (min (Y p) (Y (k+1))) (by
           exact lt_min hyp hyn)
       have hup:u < Y p:=lt_of_lt_of_le huL (min_le_left _ _)
       have hun:u < Y (k+1):=lt_of_lt_of_le huL (min_le_right _ _)
       have hpa:SA Y p u:=Or.inr ⟨by simpa [hp1] using huZ,hup⟩
       have hka:SA Y k u:=Or.inl ⟨huZ,hun⟩
       have hnepk:SX X Y p u ≠ SX X Y k u :=
         hopenne hp_lt hk_lt hpk hpa hka
       have Cp:=edgePref_eq X Y n hn hclX hclY hdiff hside hopenne hvert
         (e:=p) hp_lt hpa
       have Ck:=edgePref_eq X Y n hn hclX hclY hdiff hside hopenne hvert
         (e:=k) hk_lt hka
       rcases lt_or_gt_of_ne hnepk with hlt | hgt
       · have tpk:PT X Y p k u = 0:=by
           have hx:¬ SX X Y k u < SX X Y p u:=not_lt_of_ge hlt.le
           simp [PT,hx]
         have tkp:PT X Y k p u = -1:=by
           have dn:Y (p+1) ≤ u ∧ u < Y p:=⟨by simpa [hp1] using huZ.le,hup⟩
           have un:¬ (Y p ≤ u ∧ u < Y (p+1)):=by rw [hp1]; intro h; linarith
           simp [PT,hlt,dn,un]
         rw [sumdecomp p u,(sumat u huB).1,selfzero,tpk] at Cp
         rw [sumdecomp k u,(sumat u huB).2,selfzero,tkp] at Ck
         simpa [p] using (show EP X Y n k = EP X Y n p - 1 by linarith [Cp,Ck])
       · have tpk:PT X Y p k u = 1:=by
           have up:Y k ≤ u ∧ u < Y (k+1):=⟨huZ.le,hun⟩
           have dn:¬ (Y (k+1) ≤ u ∧ u < Y k):=by intro h; linarith
           simp [PT,hgt,up,dn]
         have tkp:PT X Y k p u = 0:=by
           have hx:¬ SX X Y p u < SX X Y k u:=not_lt_of_ge hgt.le
           simp [PT,hx]
         rw [sumdecomp p u,(sumat u huB).1,selfzero,tpk] at Cp
         rw [sumdecomp k u,(sumat u huB).2,selfzero,tkp] at Ck
         simpa [p] using (show EP X Y n k = EP X Y n p - 1 by linarith [Cp,Ck])
end H
namespace H
open scoped BigOperators
open Filter Set Topology Classical
lemma edgePref_nonneg_up_of_support
   (X Y:ℕ → ℝ) (n:ℕ) (hn:3 ≤ n)
   (hclX:X n = X 0) (hclY:Y n = Y 0)
   (hinit:Y 0 < Y 1)
   (hdiff:∀i,i < n → ∀j,j < n → i ≠ j → Y i ≠ Y j)
   (hside:∀j,j < n → Y (j+1) ≠ Y j)
   (hopenne:∀{a b:ℕ},a < n → b < n → a ≠ b → ∀{u:ℝ},SA Y a u → SA Y b u → SX X Y a u ≠ SX X Y b u)
   (hvert:∀{a t:ℕ},a < n → t < n → a ≠ t → SA Y a (Y t) → SX X Y a (Y t) ≠ X t)
   (hfirst:EP X Y n 0 = 0)
   (hlast:EP X Y n (n-1) = 0) :
   ∀e,e < n → Y e < Y (e+1) → 0 ≤ EP X Y n e:=by
 classical
 have Hinter:∀e:ℕ,e+1 < n → ((Y e < Y (e+1) → EP X Y n e = 0) ∧
      (Y (e+1) < Y e → EP X Y n e = 1)):=by
   intro e
   induction e with
   | zero =>
       intro he
       constructor
       · intro _; exact hfirst
       · intro h
         exfalso
         linarith
   | succ d IH =>
       intro he
       have hdlt:d < n:=by omega
       have hd1:d+1 < n:=by omega
       have IHd:=IH (by omega:d+1 < n)
       have R:=edgePref_next_inner X Y n (d+1) hn hclX hclY
                   hdiff hside hopenne hvert (by omega) (by omega:d+1+1 < n)
       have hprev:=hside d hdlt
       rcases lt_or_gt_of_ne hprev with hprevD | hprevU
       ·
         have Pd:EP X Y n d = 1:=IHd.2 hprevD
         constructor
         · intro hcur
           have hrel:=R.2.2.2 (by
             constructor
             · simpa using hprevD
             · simpa using hcur)
           simpa using (show EP X Y n (Nat.succ d) = (0:ℤ) by
             have hrel':EP X Y n (d+1) = EP X Y n d - 1:=by
               simpa using hrel
             norm_num [Pd] at hrel' ⊢
             exact hrel')
         · intro hcur
           have hrel:=R.2.1 (by
             constructor
             · simpa using hprevD
             · simpa using hcur)
           have hrel':EP X Y n (d+1) = EP X Y n d:=by
             simpa using hrel
           simpa [Pd] using hrel'
       ·
         have Pu:EP X Y n d = 0:=IHd.1 hprevU
         constructor
         · intro hcur
           have hrel:=R.1 (by
             constructor
             · simpa using hprevU
             · simpa using hcur)
           have hrel':EP X Y n (d+1) = EP X Y n d:=by
             simpa using hrel
           simpa [Pu] using hrel'
         · intro hcur
           have hrel:=R.2.2.1 (by
             constructor
             · simpa using hprevU
             · simpa using hcur)
           have hrel':EP X Y n (d+1) = EP X Y n d + 1:=by
             simpa using hrel
           simpa [Pu] using hrel'
 intro e he heup
 have hle:e+1 ≤ n:=by omega
 rcases lt_or_eq_of_le hle with hlt | heq
 · have hz:=(Hinter e hlt).1 heup
   rw [hz]
 · have helast:e = n-1:=by omega
   rw [helast,hlast]
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/Propagation.lean

-- BEGIN INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/FinalPolygon.lean
set_option linter.all false
namespace H
open Classical
theorem polygon_det_nonpos_of_support
   (X Y:ℕ → ℝ) (n:ℕ) (hn:3 ≤ n)
   (hXcl:X n = X 0) (hYcl:Y n = Y 0)
   (hX0:X 0 = 0) (hY0:Y 0 = 0)
   (hXnonneg:∀i:ℕ,i < n → 0 ≤ X i)
   (hYnext:0 < Y 1) (hYprev:Y (n-1) < 0)
   (hXYedges:∀i j:ℕ,i < j → j < n → ∀l m:ℝ,0 ≤ l → l < 1 → 0 ≤ m → m < 1 → ((1-l)*X i + l*X (i+1) ≠ (1-m)*X j + m*X (j+1)) ∨
       ((1-l)*Y i + l*Y (i+1) ≠ (1-m)*Y j + m*Y (j+1))) :
   (∑ i ∈ Finset.range n,(X i * Y (i+1) - Y i * X (i+1))) ≤ 0:=by
 classical
 have hXn0:X n = 0:=by simpa [hX0] using hXcl
 have hYn0:Y n = 0:=by simpa [hY0] using hYcl
 have hsep0:∀i ∈ Finset.range n,∀j ∈ Finset.range n,i ≠ j → X i ≠ X j ∨ Y i ≠ Y j:=by
   intro i hi j hj hne
   have hi':i < n:=Finset.mem_range.mp hi
   have hj':j < n:=Finset.mem_range.mp hj
   rcases lt_or_gt_of_ne hne with hij | hji
   · simpa using
       (hXYedges i j hij hj' 0 0 (by norm_num) (by norm_num)
         (by norm_num) (by norm_num))
   · have hh:=hXYedges j i hji hi' 0 0
           (by norm_num) (by norm_num) (by norm_num) (by norm_num)
     rcases hh with hh | hh
     · exact Or.inl (Ne.symm (by simpa using hh))
     · exact Or.inr (Ne.symm (by simpa using hh))
 let c:ℝ:=min (Y 1 / (|X 1| + 1))
      ((- Y (n-1)) / (|X (n-1)| + 1))
 have hc:0 < c:=by
   dsimp [c]
   apply lt_min
   · exact div_pos hYnext (by have:=abs_nonneg (X 1); linarith)
   · exact div_pos (by linarith [hYprev])
         (by have:=abs_nonneg (X (n-1)); linarith)
 obtain ⟨q,hq,hlev⟩ :=
   H.exists_small_shear X Y (Finset.range n) hsep0 hc
 let Z:ℕ → ℝ:=fun i => Y i + q*X i
 have hZ0:Z 0 = 0:=by simp [Z,hX0,hY0]
 have hZn0:Z n = 0:=by simp [Z,hXn0,hYn0]
 have hqA:|q| < Y 1 / (|X 1|+1):=by
   exact lt_of_lt_of_le hq (by dsimp [c]; exact min_le_left _ _)
 have hqD:|q| < (-Y (n-1)) / (|X (n-1)|+1):=by
   exact lt_of_lt_of_le hq (by dsimp [c]; exact min_le_right _ _)
 have hzends:0 < Z 1 ∧ Z (n-1) < 0:=by
   have hh:=H.shear_end_signs hYnext hYprev hqA hqD
   simpa [Z] using hh
 have hzdiff:∀i < n,∀j < n,i ≠ j → Z i ≠ Z j:=by
   intro i hi j hj hh
   dsimp [Z]
   exact hlev i (Finset.mem_range.mpr hi)
       j (Finset.mem_range.mpr hj) hh
 have hZedges :
     ∀i j:ℕ,i < j → j < n → ∀l m:ℝ,0 ≤ l → l < 1 → 0 ≤ m → m < 1 → ((1-l)*X i + l*X (i+1) ≠
             (1-m)*X j + m*X (j+1)) ∨
         ((1-l)*Z i + l*Z (i+1) ≠
             (1-m)*Z j + m*Z (j+1)):=by
   intro i j hij hj l m hl0 hl1 hm0 hm1
   have old:=hXYedges i j hij hj l m hl0 hl1 hm0 hm1
   by_contra hh
   push Not at hh
   rcases hh with ⟨hx,hz⟩
   apply Or.elim old
   · intro hbad
     exact hbad hx
   · intro hybad
     have holdaff:(1-l)*Y i + l*Y (i+1) =
             (1-m)*Y j + m*Y (j+1):=by
       have both :
           ((1-l)*X i + l*X (i+1) =
               (1-m)*X j + m*X (j+1) ∧
             (1-l)*(Y i+q*X i) + l*(Y (i+1)+q*X (i+1)) =
               (1-m)*(Y j+q*X j) + m*(Y (j+1)+q*X (j+1))):=by
         exact ⟨hx,by simpa [Z] using hz⟩
       exact
         (H.shear_affine_eq_iff
           (X i) (X (i+1)) (Y i) (Y (i+1))
           (X j) (X (j+1)) (Y j) (Y (j+1)) q l m).mp both |>.2
     exact hybad holdaff
 have hslicene :
     ∀{i j:ℕ},i < j → j < n → ∀{w:ℝ},
       H.SA Z i w → H.SA Z j w → H.SX X Z i w ≠
         H.SX X Z j w:=by
   intro i j hij hj w hi hjw
   exact H.slice_ne_of_halfopen X Z hZedges hij hj hi hjw
 have hXall:∀i ≤ n,0 ≤ X i:=by
   intro i hi
   rcases lt_or_eq_of_le hi with hi | hi
   · exact hXnonneg i hi
   · rw [hi,hXn0]
 have hXslice_nonneg :
     ∀{i:ℕ},i < n → ∀{w:ℝ},
       H.SA Z i w → 0 ≤ H.SX X Z i w:=by
   intro i hi w hw
   have hp:=H.param_pos_lt_one hw
   have hi1:i + 1 ≤ n:=by omega
   dsimp [H.SX]
   have h1:0 ≤ (1 - H.SP Z i w):=by linarith
   have h2:0 ≤ H.SP Z i w:=hp.1.le
   have A:0 ≤ (1 - H.SP Z i w) * X i :=
     mul_nonneg h1 (hXall i hi.le)
   have B:0 ≤ H.SP Z i w * X (i+1) :=
     mul_nonneg h2 (hXall (i+1) hi1)
   linarith
 have hvertex_slice_ne:∀{a k:ℕ},a < n → k < n → a ≠ k → H.SA Z a (Z k) → H.SX X Z a (Z k) ≠ X k:=by
   intro a k ha hk hak hact
   exact H.slice_vertex_ne_of_halfopen X Z hZedges
     ha hk hak (z:= Z k) rfl hact
 have hxsect:∀i,i < n → ∀w,H.SA Z i w → 0 ≤ H.SX X Z i w:=by
   intro i hi w hw
   exact hXslice_nonneg hi hw
 have hmatching:∀(w:ℝ),
       (∀i:ℕ,i < n → Z i ≠ w) → ∃g:ℕ → ℕ,
         Set.InjOn g (↑(H.UE Z n w):Set ℕ) ∧
         (∀i ∈ H.UE Z n w,
             g i ∈ H.DE Z n w ∧
             H.SX X Z i w ≤
                H.SX X Z (g i) w):=by
   intro w hwreg
   let U:Finset ℕ:=H.UE Z n w
   let T:Finset ℕ:=H.DE Z n w
   let v:ℕ → ℝ:=fun i => H.SX X Z i w
   have hwreg':∀i,i ≤ n → Z i ≠ w:=by
     intro i hi
     rcases lt_or_eq_of_le hi with hlt | hEq
     · exact hwreg i hlt
     · subst i
       simpa [hZn0,hZ0] using (hwreg 0 (by omega))
   have hcard:U.card = T.card:=by
     dsimp [U,T]
     exact H.card_up_eq_card_down_regular Z n w
       (by rw [hZn0,hZ0]) hwreg'
   have hprefix:∀i ∈ U,
       (T.filter (fun k => v k < v i)).card ≤
          (U.filter (fun k => v k < v i)).card:=by
     have hsideY:∀j:ℕ,j < n → Z (j+1) ≠ Z j:=by
       intro j hj
       by_cases ht:j+1 < n
       · exact hzdiff (j+1) ht j hj (by omega)
       · have heq:j+1 = n:=by omega
         have hj0:j ≠ 0:=by omega
         rw [heq,hZn0]
         have hh:=hzdiff 0 (by omega) j hj (Ne.symm hj0)
         simpa [hZ0] using hh
     intro i hi
     have hUi:i ∈ H.UE Z n w:=by
       simpa [U] using hi
     have his:H.SA Z i w :=
       Or.inl ((H.mem_upEdges).1 hUi).2
     have hcount:=H.pref_eq_counts X Z n i w hwreg'
     change H.pref X Z n i w =
         ((U.filter (fun j => H.SX X Z j w <
             H.SX X Z i w)).card:ℤ) -
         ((T.filter (fun j => H.SX X Z j w <
             H.SX X Z i w)).card:ℤ) at hcount
     have hremain:0 ≤ H.pref X Z n i w:=by
       have hdiff':∀a,a < n → ∀b,b < n → a ≠ b → Z a ≠ Z b:=by
         intro a ha b hb hh
         exact hzdiff a ha b hb hh
       have hopen':∀{a b:ℕ},a < n → b < n → a ≠ b → ∀{t:ℝ},H.SA Z a t → H.SA Z b t → H.SX X Z a t ≠
                   H.SX X Z b t:=by
         intro a b ha hb hab t hat hbt
         rcases Nat.lt_or_gt_of_ne hab with hlt|hgt
         · exact hslicene hlt hb hat hbt
         · exact Ne.symm (hslicene hgt ha hbt hat)
       have hvert':∀{a k:ℕ},a < n → k < n → a ≠ k → H.SA Z a (Z k) → H.SX X Z a (Z k) ≠ X k:=by
         intro a k ha hk hh hh'
         exact hvertex_slice_ne ha hk hh hh'
       have C:=H.edgePref_eq X Z n hn
             (by rw [hXcl]) (by rw [hZn0,hZ0])
             hdiff' hsideY hopen' hvert' (e:=i)
             ((H.mem_upEdges).1 hUi).1 his
       rw [C]
       have hfinite:∀e:ℕ,e < n → Z e < Z (e+1) → 0 ≤ H.EP X Z n e:=by
         have hfirst:H.EP X Z n 0 = 0:=by
           apply H.edgePref_zero_first_of_support
             X Z n hn
             hXcl (by rw [hZn0,hZ0]) hX0 hZ0 hzends.1 hzends.2
             hXall
           · intro a ha b hb hab
             exact hzdiff a ha b hb hab
           · exact hsideY
           · intro a b ha hb hab u hua hub
             rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
             · exact hslicene hlt hb hua hub
             · exact Ne.symm (hslicene hgt ha hub hua)
           · intro a b ha hb hab hact
             exact hvertex_slice_ne ha hb hab hact
         have hlast:H.EP X Z n (n-1) = 0:=by
           apply H.edgePref_zero_last_of_support
             X Z n hn
             hXcl (by rw [hZn0,hZ0]) hX0 hZ0 hzends.1 hzends.2
             hXall
           · intro a ha b hb hab
             exact hzdiff a ha b hb hab
           · exact hsideY
           · intro a b ha hb hab u hua hub
             rcases Nat.lt_or_gt_of_ne hab with hlt | hgt
             · exact hslicene hlt hb hua hub
             · exact Ne.symm (hslicene hgt ha hub hua)
           · intro a b ha hb hab hact
             exact hvertex_slice_ne ha hb hab hact
         exact H.edgePref_nonneg_up_of_support
           X Z n hn hXcl (by rw [hZn0,hZ0])
           (by simpa [hZ0] using hzends.1)
           hdiff' hsideY hopen' hvert' hfirst hlast
       exact hfinite i ((H.mem_upEdges).1 hUi).1
            (lt_trans ((H.mem_upEdges).1 hUi).2.1
              ((H.mem_upEdges).1 hUi).2.2)
     have hcnt_nonneg :
         (0:ℤ) ≤
           (((U.filter (fun j =>
                H.SX X Z j w < H.SX X Z i w)).card:ℕ):ℤ) -
           (((T.filter (fun j =>
                H.SX X Z j w < H.SX X Z i w)).card:ℕ):ℤ):=by
       rw [← hcount]
       exact hremain
     have hcnt_le :
         (( (T.filter (fun j =>
                H.SX X Z j w <
                  H.SX X Z i w)).card:ℕ):ℤ) ≤
         (( (U.filter (fun j =>
                H.SX X Z j w <
                  H.SX X Z i w)).card:ℕ):ℤ):=by
       omega
     have hcnt_nat :
         (T.filter (fun j =>
                H.SX X Z j w <
                  H.SX X Z i w)).card ≤
         (U.filter (fun j =>
                H.SX X Z j w <
                  H.SX X Z i w)).card:=by
       exact_mod_cast hcnt_le
     simpa [v] using hcnt_nat
   have hsuffix:∀i ∈ U,
       (U.filter (fun k => v i ≤ v k)).card ≤
          (T.filter (fun k => v i ≤ v k)).card:=by
     intro i hi
     have hu:=Finset.card_filter_add_card_filter_not
         (s:=U) (fun k => v k < v i)
     have ht:=Finset.card_filter_add_card_filter_not
         (s:=T) (fun k => v k < v i)
     have hnotu:U.filter (fun k => ¬ v k < v i) =
             U.filter (fun k => v i ≤ v k):=by
       ext k
       simp
     have hnott:T.filter (fun k => ¬ v k < v i) =
             T.filter (fun k => v i ≤ v k):=by
       ext k
       simp
     rw [hnotu] at hu
     rw [hnott] at ht
     have hp:=hprefix i hi
     omega
   rcases H.exists_right_matching_of_suffix U T v hsuffix with
     ⟨g,hg,hgp⟩
   refine ⟨g,?_,?_⟩
   · simpa [U] using hg
   · intro i hi
     have hi':i ∈ U:=by simpa [U] using hi
     have hh:=hgp i hi'
     dsimp [v] at hh
     simpa [T] using hh
 have hsw:∀w:ℝ,
       (∀i:ℕ,i < n → Z i ≠ w) → H.SV X Z n w ≤ 0:=by
   intro w hw
   exact H.sweep_nonpos_of_matching_at X Z n w hxsect
     (hmatching w hw)
 have hnotZ:(∑ i ∈ Finset.range n,
       (X i * Z (i+1) - Z i * X (i+1))) ≤ 0 :=
   H.det_nonpos_of_regular_sweep X Z n hXcl (by rw [hZn0,hZ0])
     (by
       intro w hw
       exact hsw w hw)
 have heq:(∑ i ∈ Finset.range n,
       (X i * Z (i+1) - Z i * X (i+1))) =
       (∑ i ∈ Finset.range n,
       (X i * Y (i+1) - Y i * X (i+1))):=by
   apply Finset.sum_congr rfl
   intro i hi
   have hterm:=H.det_shear
       (X i) (Y i) (X (i+1)) (Y (i+1)) q
   dsimp [Z]
   nlinarith [hterm]
 rw [heq] at hnotZ
 exact hnotZ
end H

-- END INLINED FILE: Mathlib/Support/hopf_umlaufsatz_09c00d2fe1/FinalPolygon.lean

-- BEGIN INLINED FILE: Main.lean

open LeanEval.Geometry.HopfUmlaufsatz
set_option maxHeartbeats 2000000
set_option linter.all false

namespace Submission

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem hopf_umlaufsatz {r : ℝ → Plane} {α : ℝ → ℝ}
    (_hr : IsPositiveSimpleClosedUnitSpeedCurve r)
    (_hα : IsTangentAngleLift r α) :
    totalCurvature α = 2 * Real.pi :=
/-ResultProofBegin-/ by
 have hFTC:totalCurvature α = α period - α 0:=by
   change (∫ t in (0:ℝ)..period,deriv α t) = _
   exact H.integral_deriv_contDiff_one α _hα.smooth 0 period
 have hvel:velocity r period = velocity r 0:=by
   unfold velocity
   have hd:Differentiable ℝ r :=
     _hr.smooth.differentiable (by exact one_ne_zero)
   exact H.deriv_period_endpoint r hd period _hr.periodic
 have hvec :
     !₂[Real.cos (α period),Real.sin (α period)] =
       !₂[Real.cos (α 0),Real.sin (α 0)]:=by
   simpa [_hα.velocity_eq] using hvel
 have hcos:Real.cos (α 0) = Real.cos (α period):=by
   have h:=congrArg (fun v:Plane => v 0) hvec
   simpa using h.symm
 have hsin:Real.sin (α 0) = Real.sin (α period):=by
   have h:=congrArg (fun v:Plane => v 1) hvec
   simpa using h.symm
 obtain ⟨N,hN⟩ :=
   H.angle_eq_mod_two_pi (α 0) (α period) hcos hsin
 have hvelAll (t:ℝ):velocity r (t+period) = velocity r t:=by
   unfold velocity
   have hd:Differentiable ℝ r :=
     _hr.smooth.differentiable (by exact one_ne_zero)
   exact H.deriv_period_add r hd period _hr.periodic t
 have hcosAll (t:ℝ):Real.cos (α t) = Real.cos (α (t+period)):=by
   have hv:=hvelAll t
   have hv' :
       !₂[Real.cos (α (t+period)),Real.sin (α (t+period))] =
         !₂[Real.cos (α t),Real.sin (α t)]:=by
     simpa [_hα.velocity_eq] using hv
   have h:=congrArg (fun v:Plane => v 0) hv'
   simpa using h.symm
 have hsinAll (t:ℝ):Real.sin (α t) = Real.sin (α (t+period)):=by
   have hv:=hvelAll t
   have hv' :
       !₂[Real.cos (α (t+period)),Real.sin (α (t+period))] =
         !₂[Real.cos (α t),Real.sin (α t)]:=by
     simpa [_hα.velocity_eq] using hv
   have h:=congrArg (fun v:Plane => v 1) hv'
   simpa using h.symm
 have hinc:∀t:ℝ,α (t+period) - α t = α (0+period) - α 0 :=
   H.angle_increment_constant α _hα.smooth.continuous period hcosAll hsinAll
 have hall (t:ℝ) :
     α (t+period) = (N:ℝ) * (2 * Real.pi) + α t:=by
   have hi:=hinc t
   have hzero:α (0+period) = (N:ℝ) * (2 * Real.pi) + α 0:=by
     simpa using hN
   rw [hzero] at hi
   linarith
 have hp0:0 < period:=by
   unfold period
   positivity
 have hturn:N = (1:ℤ):=by
   have hderr:∀x:ℝ,
       deriv r x = !₂[Real.cos (α x),Real.sin (α x)]:=by
     intro x
     simpa [velocity] using (_hα.velocity_eq x)
   have hunit':∀x:ℝ,‖deriv r x‖ = 1:=by
     intro x
     simpa [velocity] using (_hr.unit_speed x)
   obtain ⟨s,hs0,hsp,hsupp⟩ :=
     H.exists_left_support_shift r hp0 _hr.smooth _hr.periodic
   let f:ℝ → Plane:=fun t => r (t+s)
   let A:ℝ → ℝ:=fun t => α (t+s)
   have hf:ContDiff ℝ 1 f:=by
     dsimp [f]
     have hi:ContDiff ℝ 1 (fun t:ℝ => t+s) :=
       (by fun_prop:ContDiff ℝ 1 (fun t:ℝ => t+s))
     simpa [Function.comp_def] using (_hr.smooth.comp hi)
   have hA:Continuous A:=by
     dsimp [A]
     have hi:Continuous (fun t:ℝ => t+s):=by fun_prop
     exact _hα.smooth.continuous.comp hi
   have hfp:Function.Periodic f period:=by
     intro t; dsimp [f]
     simpa [add_assoc,add_comm,add_left_comm] using (_hr.periodic (t+s))
   have hfi:Set.InjOn f (Set.Ico (0:ℝ) period) :=
     H.injOn_shift_Ico r hp0 hs0 hsp _hr.periodic _hr.injective_on_period
   have hfa:∀x:ℝ,deriv f x =
        !₂[Real.cos (A x),Real.sin (A x)]:=by
     intro x
     dsimp [f,A]
     rw [H.deriv_shift r (_hr.smooth.differentiable (by exact one_ne_zero)) s x]
     exact hderr (x+s)
   have hfmin:∀x ∈ Set.Icc (0:ℝ) period,f 0 0 ≤ f x 0:=by
     intro x hx
     simpa [f] using hsupp x hx
   have hfd0:deriv f 0 0 = 0 :=
     H.deriv0_coord_of_left_support f hp0 hf hfp hfmin
   obtain ⟨q,hqcases,hq⟩ :=
     H.tangent_turn_support_pm f A hp0 hf hA hfp hfi hfa hfmin hfd0
   have heqS:A period - A 0 = (N:ℝ) * (2*Real.pi):=by
     have hi:=hall s
     dsimp [A]
     rw [show period + s = s + period by ring]
     simpa using (show α (s+period) - α s = (N:ℝ) * (2*Real.pi) by linarith)
   have heqN:(N:ℝ) = (((2*q+1:ℤ):ℝ)):=by
     dsimp [A] at hq
     rw [heqS] at hq
     have hpival:0 < Real.pi:=Real.pi_pos
     push_cast at hq ⊢
     nlinarith
   have hNZ:N = 2*q+1:=by exact_mod_cast heqN
   have hpm:N = (1:ℤ) ∨ N = -1:=by
     rcases hqcases with hh | hh
     · left; omega
     · right; omega
   rcases hpm with hplus | hminus
   · exact hplus
   ·
     have hAneg:A period - A 0 = -(2*Real.pi):=by
       have hi:=hall s
       dsimp [A]
       have hnreal:(N:ℝ) = -1:=by exact_mod_cast hminus
       rw [show period + s = s + period by ring]
       rw [hi,hnreal]
       ring
     have hup:Real.sin (A 0) = 1 :=
       H.left_support_sin_one_of_turn_neg f A hp0 hf hA hfp hfi
         hfa hfmin hfd0 hAneg
     have harea0:0 <
         (∫ t in (0:ℝ)..period,
           H.DP (r t) (deriv r t)):=by
       have hh:=_hr.positive_orientation
       dsimp [signedArea,det2,velocity] at hh
       change 0 < (1 / 2:ℝ) *
           (∫ t in (0:ℝ)..period,
             H.DP (r t) (deriv r t)) at hh
       nlinarith
     have harea:0 <
         (∫ t in (0:ℝ)..period,
           H.DP (f t) (deriv f t)):=by
       have he:=H.integral_detPlane_shift r _hr.smooth _hr.periodic s
       dsimp [f]
       rw [he]
       exact harea0
     have hxde :
         (∫ t in (0:ℝ)..period,
           H.DP (f t) (deriv f t)) =
          2 * ∫ t in (0:ℝ)..period,
             (f t 0 - f 0 0) * (deriv f t) 1 :=
       H.area_as_offset_xdy f hf hfp (f 0 0)
     have hxpos:0 < ∫ t in (0:ℝ)..period,
             (f t 0 - f 0 0) * (deriv f t) 1:=by
       rw [hxde] at harea
       linarith
     have hderup:deriv f 0 = !₂[(0:ℝ),(1:ℝ)]:=by
       have hv:=hfa 0
       have hc:=congrArg (fun z:Plane => z 0) hv
       have hs:=congrArg (fun z:Plane => z 1) hv
       rw [hup] at hs
       rw [hfd0] at hc
       have hc0:Real.cos (A 0) = 0:=by simpa using hc.symm
       rw [hc0] at hv
       rw [hup] at hv
       exact hv
     have hdupy:(deriv f 0) 1 = (1:ℝ):=by
       have h:=congrArg (fun z:Plane => z 1) hderup
       simpa using h
     obtain ⟨δ,hδ0,hδp,hyfirst,hylast⟩ :=
       H.up_tangent_y_near_endpoints f hp0 hf hfp hdupy
     have hfu:∀t:ℝ,‖deriv f t‖ = (1:ℝ):=by
       intro t
       dsimp [f]
       rw [H.deriv_shift r
             (_hr.smooth.differentiable (by exact one_ne_zero)) s t]
       exact hunit' (t+s)
     obtain ⟨n,hn,hstep0,hstepδ,hy0',hy1',hxv,hedges,hsum⟩ :=
       H.exists_positive_simple_support_mesh f hp0 hf hfp hfi
         hfu hfmin hδ0 hδp
         (by intro t ht htδ; exact hyfirst t ht htδ)
         (by intro t ht htp; exact hylast t ht htp)
         hxpos
     rcases hsum with ⟨hsum,htrap⟩
     let D:ℝ:=period / (n:ℝ)
     have hn3:3 ≤ n:=by
       have hn1:n ≠ 1:=by
         intro he
         subst n
         have hfp0:f period = f 0:=by simpa using hfp 0
         have hD:period / ((1:ℕ):ℝ) = period:=by norm_num
         rw [hD,hfp0] at hy0'
         exact (lt_irrefl _ hy0')
       have hn2:n ≠ 2:=by
         intro he
         subst n
         have heq:period - period / ((2:ℕ):ℝ) = period / ((2:ℕ):ℝ):=by
           push_cast
           ring
         rw [heq] at hy1'
         exact (not_lt_of_ge (le_of_lt hy0') hy1')
       omega
     let V:ℕ → Plane:=fun i => f ((i:ℝ)*D)
     have hn1le:1 ≤ n:=by omega
     have hpD:(n:ℝ)*D = period:=by
       dsimp [D]
       have hnR:(n:ℝ) ≠ 0:=by exact_mod_cast (ne_of_gt hn)
       exact (mul_div_cancel₀ _ hnR)
     have hVend:V n = V 0:=by
       dsimp [V]
       rw [hpD]
       simpa using hfp 0
     have hVdistinct:∀i j:ℕ,i < j → j < n → V i ≠ V j:=by
       intro i j hij hj
       have he:=hedges i j hij hj (0:ℝ) (0:ℝ)
         (by norm_num) (by norm_num) (by norm_num) (by norm_num)
       simpa [V,D] using he
     have hVx:∀i:ℕ,i < n → 0 ≤ (V i) 0 - (V 0) 0:=by
       intro i hi
       have hh:=hxv i hi
       simpa [V,D] using hh
     have hVnext:(V 0) 1 < (V 1) 1:=by
       simpa [V,D] using hy0'
     have hVprev:(V (n-1)) 1 < (V 0) 1:=by
       have hcsub:(((n-1:ℕ):ℝ) * D) = period - D:=by
         rw [Nat.cast_sub hn1le]
         push_cast
         rw [sub_mul,hpD]
         ring
       dsimp [V]
       rw [hcsub]
       simpa [D] using hy1'
     have hVedges :
         ∀i j:ℕ,i < j → j < n → ∀l m:ℝ,0 ≤ l → l < 1 → 0 ≤ m → m < 1 → V i + l • (V (i+1) - V i) ≠
               V j + m • (V (j+1) - V j):=by
       intro i j hij hj l m l0 l1 m0 m1
       simpa [V,D] using (hedges i j hij hj l m l0 l1 m0 m1)
     have htrapV:0 < ∑ i ∈ Finset.range n,
           ((((V i) 0 - (V 0) 0) +
               ((V (i+1)) 0 - (V 0) 0)) / 2) *
             ((V (i+1)) 1 - (V i) 1):=by
       simpa [V,D] using htrap
     let X:ℕ → ℝ:=fun i => (V i) 0 - (V 0) 0
     let Y:ℕ → ℝ:=fun i => (V i) 1 - (V 0) 1
     have hXcl:X n = X 0:=by dsimp [X]; rw [hVend]
     have hYcl:Y n = Y 0:=by dsimp [Y]; rw [hVend]
     have hdet:0 < ∑ i ∈ Finset.range n,
           (X i * Y (i+1) - Y i * X (i+1)):=by
       have ht:=H.trapezoid_eq_half_det X Y n hXcl hYcl
       have he :
           (∑ i ∈ Finset.range n,
             ((((V i) 0 - (V 0) 0) +
                ((V (i+1)) 0 - (V 0) 0)) / 2) *
                ((V (i+1)) 1 - (V i) 1)) =
            (∑ i ∈ Finset.range n,
               (X i * Y (i+1) - Y i * X (i+1))) / 2:=by
         convert ht using 1 <;> simp [X,Y]
       linarith [htrapV]
     have hX0:X 0 = 0:=by simp [X]
     have hY0:Y 0 = 0:=by simp [Y]
     have hXnonneg:∀i:ℕ,i < n → 0 ≤ X i:=by
       intro i hi
       simpa [X] using hVx i hi
     have hYnext':0 < Y 1:=by
       dsimp [Y]
       linarith [hVnext]
     have hYprev':Y (n-1) < 0:=by
       dsimp [Y]
       linarith [hVprev]
     have hXYedges :
         ∀i j:ℕ,i < j → j < n → ∀l m:ℝ,0 ≤ l → l < 1 → 0 ≤ m → m < 1 → ((1-l)*X i + l*X (i+1) ≠ (1-m)*X j + m*X (j+1)) ∨
             ((1-l)*Y i + l*Y (i+1) ≠ (1-m)*Y j + m*Y (j+1)):=by
       intro i j hij hj l m l0 l1 m0 m1
       have hvne:=hVedges i j hij hj l m l0 l1 m0 m1
       by_contra hbad
       push Not at hbad
       rcases hbad with ⟨hx,hy⟩
       apply hvne
       ext z
       fin_cases z
       · dsimp [X] at hx
         simp at hx ⊢
         linarith
       · dsimp [Y] at hy
         simp at hy ⊢
         linarith
     exfalso
     have hnot:=H.polygon_det_nonpos_of_support
       X Y n hn3 hXcl hYcl hX0 hY0 hXnonneg hYnext' hYprev' hXYedges
     exact (not_lt_of_ge hnot) hdet
 have hdiff:α period - α 0 = (2:ℝ) * Real.pi:=by
   rw [hN,hturn]
   norm_num
 rw [hFTC,hdiff]
/-ResultProofEnd-/
/-ResultEnd-/

end Submission

-- END INLINED FILE: Main.lean
