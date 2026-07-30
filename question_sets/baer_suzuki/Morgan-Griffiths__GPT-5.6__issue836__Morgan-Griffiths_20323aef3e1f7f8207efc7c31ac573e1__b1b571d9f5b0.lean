import ChallengeDeps

-- BEGIN INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/Forward.lean
section

namespace Foo
open scoped Classical

lemma sup_core_normal {G : Type*} [Group G] (p : ℕ) :
  (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} : Subgroup G).Normal := by
  apply Subgroup.sSup_normal
  intro H hH
  exact hH.1

lemma sup_core_isPGroup {G : Type*} [Group G] (p : ℕ) :
  IsPGroup p (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} : Subgroup G) := by
  apply Sylow.sSup_of_normal
  · intro H hH
    exact hH.2
  · intro H hH
    exact hH.1

/-- Membership in the largest normal `p`-subgroup is preserved by any
    multiplicative equivalence of the ambient groups.  This makes it possible
    to transport the minimal-counterexample assertions to conjugate, hence
    isomorphic, overgroups.

    No finiteness (and no primality of `p`) is required here: the image of the
    core of `K` under `f` is a normal `p`-subgroup of `L`, and therefore lies in
    the core of `L`.  Apply the same argument to `f.symm` for the converse. -/
lemma mem_sup_core_equiv {K L : Type*} [Group K] [Group L]
    (f : K ≃* L) (p : ℕ) (y : K) :
    y ∈ (sSup {N : Subgroup K | N.Normal ∧ IsPGroup p N} : Subgroup K) ↔
      f y ∈ (sSup {M : Subgroup L | M.Normal ∧ IsPGroup p M} : Subgroup L) := by
  let CK : Subgroup K :=
    (sSup {N : Subgroup K | N.Normal ∧ IsPGroup p N} : Subgroup K)
  let CL : Subgroup L :=
    (sSup {M : Subgroup L | M.Normal ∧ IsPGroup p M} : Subgroup L)
  have CKn : CK.Normal := sup_core_normal p
  have CKp : IsPGroup p CK := sup_core_isPGroup p
  have CLn : CL.Normal := sup_core_normal p
  have CLp : IsPGroup p CL := sup_core_isPGroup p
  have mapKL : CK.map f.toMonoidHom ≤ CL := by
    have hn : (CK.map f.toMonoidHom).Normal :=
      CKn.map f.toMonoidHom f.surjective
    have hp : IsPGroup p (CK.map f.toMonoidHom) :=
      IsPGroup.map CKp f.toMonoidHom
    apply le_sSup
    exact ⟨hn, hp⟩
  have mapLK : CL.map f.symm.toMonoidHom ≤ CK := by
    have hn : (CL.map f.symm.toMonoidHom).Normal :=
      CLn.map f.symm.toMonoidHom f.symm.surjective
    have hp : IsPGroup p (CL.map f.symm.toMonoidHom) :=
      IsPGroup.map CLp f.symm.toMonoidHom
    apply le_sSup
    exact ⟨hn, hp⟩
  constructor
  · intro hy
    have hy' : y ∈ CK := by simpa [CK] using hy
    have hmem : f y ∈ CK.map f.toMonoidHom := by
      exact ⟨y, hy', rfl⟩
    have hz : f y ∈ CL := mapKL hmem
    simpa [CL] using hz
  · intro hy
    have hy' : f y ∈ CL := by simpa [CL] using hy
    have hmem : f.symm (f y) ∈ CL.map f.symm.toMonoidHom := by
      exact ⟨f y, hy', rfl⟩
    have hz : f.symm (f y) ∈ CK := mapLK hmem
    have hz' : y ∈ CK := by
      simpa using hz
    simpa [CK] using hz'

/-- If every proper overgroup of `x` has `x` in its own `p`-core, the
    same assertion holds for a conjugate `g*x*g⁻¹` and its proper
    overgroups.  One conjugates the overgroup back by `g⁻¹` and uses
    `mem_sup_core_equiv` on the resulting equivalence of subgroup types.

    This small transport lemma contains no finiteness or generation
    assumptions; it is convenient precisely in a minimal-counterexample
    argument where `hproper` is available only for overgroups of the chosen
    representative `x`. -/
lemma conj_mem_sup_core_of_hproper {G : Type*} [Group G] {p : ℕ} {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x, hxH⟩ : H) ∈
        (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H))
    (g : G) (T : Subgroup G) (hy : g * x * g⁻¹ ∈ T) (hT : T ≠ ⊤) :
    (⟨g * x * g⁻¹, hy⟩ : T) ∈
      (sSup {Q : Subgroup T | Q.Normal ∧ IsPGroup p Q} : Subgroup T) := by
  classical
  -- Pull `T` back by the inverse conjugation; this overgroup contains `x`.
  let φ : G ≃* G := (MulAut.conj g)
  let ψ : G ≃* G := (MulAut.conj (g⁻¹))
  have hφψ : ∀ z : G, φ (ψ z) = z := by
    intro z
    simp [φ, ψ, MulAut.conj_apply, mul_assoc]
  have hψφ : ∀ z : G, ψ (φ z) = z := by
    intro z
    simp [φ, ψ, MulAut.conj_apply, mul_assoc]
  let S : Subgroup G := T.map ψ.toMonoidHom
  have hxS : x ∈ S := by
    change x ∈ T.map ψ.toMonoidHom
    refine ⟨g * x * g⁻¹, hy, ?_⟩
    change ψ (g * x * g⁻¹) = x
    simp [ψ, mul_assoc]
  have hS : S ≠ (⊤ : Subgroup G) := by
    intro hs
    apply hT
    apply (Subgroup.eq_top_iff' T).2
    intro t
    -- Since `S` is top, `ψ t` belongs to it.  Unpack the definition
    -- `S = T.map ψ` to recover an element of `T` with image `ψ t`.
    have htS : ψ t ∈ S := by
      rw [hs]
      exact Subgroup.mem_top _
    change ψ t ∈ T.map ψ.toMonoidHom at htS
    rcases htS with ⟨u, hu, heq⟩
    have hut : u = t := ψ.injective heq
    simpa [hut] using hu
  have hto (z : S) : φ (z : G) ∈ T := by
    have hz := z.property
    change (z : G) ∈ T.map ψ.toMonoidHom at hz
    rcases hz with ⟨u, hu, heq⟩
    change φ (z : G) ∈ T
    rw [← heq]
    simpa [hφψ] using hu
  have hfrom (t : T) : ψ (t : G) ∈ S := by
    change ψ (t : G) ∈ T.map ψ.toMonoidHom
    exact ⟨(t : G), t.property, rfl⟩
  -- Restrict conjugation to the two subgroup types.  The definitions make
  -- the underlying formula visible when we later evaluate at `x`.
  let e : S ≃* T :=
    { toFun := fun z => ⟨φ (z : G), hto z⟩
      invFun := fun t => ⟨ψ (t : G), hfrom t⟩
      left_inv := by
        intro z
        apply Subtype.ext
        change ψ (φ (z : G)) = (z : G)
        exact hψφ (z : G)
      right_inv := by
        intro t
        apply Subtype.ext
        change φ (ψ (t : G)) = (t : G)
        exact hφψ (t : G)
      map_mul' := by
        intro a b
        apply Subtype.ext
        change φ ((a : G) * (b : G)) = φ (a : G) * φ (b : G)
        exact map_mul φ (a : G) (b : G) }
  have hex :=
    (mem_sup_core_equiv e p (⟨x, hxS⟩ : S)).1 (hproper S hxS hS)
  have heq : e (⟨x, hxS⟩ : S) = (⟨g * x * g⁻¹, hy⟩ : T) := by
    apply Subtype.ext
    change φ x = g * x * g⁻¹
    simp [φ, MulAut.conj_apply]
  rw [heq] at hex
  exact hex

lemma forward {G : Type*} [Group G] (p:ℕ) (x:G) 
  (hx : x ∈ (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} : Subgroup G)) :
  ∀ g : G, IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G)) := by
  let C : Subgroup G := sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}
  have hC_N : C.Normal := sup_core_normal p
  letI : C.Normal := hC_N
  have hC_P : IsPGroup p C := sup_core_isPGroup p
  intro g
  apply IsPGroup.to_le hC_P
  apply (Subgroup.closure_le C).mpr
  intro y hy
  have hy' : y = x ∨ y = g * x * g⁻¹ := by simpa using hy
  rcases hy' with h | h
  · simpa [C, h] using hx
  · rw [h]
    exact hC_N.conj_mem x (by simpa [C] using hx) g

end Foo

namespace Foo
lemma pair_hyp_is_p_elem {G : Type*} [Group G] {p : ℕ} (x : G)
    (h : ∀ g : G, IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    ∃ k : ℕ, x ^ p ^ k = 1 := by
  have hx : x ∈ (Subgroup.closure ({x, (1:G) * x * (1:G)⁻¹} : Set G)) := by
    apply Subgroup.subset_closure
    simp
  rcases h 1 ⟨x, hx⟩ with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have := congrArg (fun y : Subgroup.closure ({x, (1:G) * x * (1:G)⁻¹} : Set G) => (y : G)) hk
  simpa using this
end Foo
namespace Foo
lemma pair_exists_sylow {G : Type*} [Group G] {p : ℕ} (x g : G)
    (h : IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    ∃ P : Sylow p G, x ∈ P ∧ g * x * g⁻¹ ∈ P := by
  rcases h.exists_le_sylow with ⟨P, hP⟩
  refine ⟨P, hP ?_, hP ?_⟩
  · apply Subgroup.subset_closure
    simp
  · apply Subgroup.subset_closure
    simp
end Foo
namespace Foo
lemma mem_sup_core_iff_normalclosure {G : Type*} [Group G] (p : ℕ) (x : G) :
  x ∈ (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} : Subgroup G) ↔
    IsPGroup p (Subgroup.normalClosure ({x} : Set G)) := by
  let C : Subgroup G := sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}
  have Cn : C.Normal := sup_core_normal p
  letI : C.Normal := Cn
  have Cp : IsPGroup p C := sup_core_isPGroup p
  constructor
  · intro hx
    apply IsPGroup.to_le Cp
    apply Subgroup.normalClosure_le_normal
    intro y hy
    have hy' : y = x := by simpa using hy
    simpa [C, hy'] using hx
  · intro h
    -- normal closure among family, hence contained
    have hle : Subgroup.normalClosure ({x}: Set G) ≤ C := by
      apply le_sSup -- maybe order? #check
      exact ⟨by infer_instance, h⟩
    apply hle
    exact Subgroup.subset_normalClosure (by simp)
end Foo
namespace Foo
open scoped Pointwise
-- lemma iInf Sylow normal
lemma sylow_iInf_normal {G : Type*} [Group G] (p : ℕ) :
  (⨅ P : Sylow p G, (P : Subgroup G)).Normal := by
  let T : Subgroup G := ⨅ P : Sylow p G, (P : Subgroup G)
  -- need build
  change T.Normal
  refine ⟨?_⟩
  intro n hn g
  apply Subgroup.mem_iInf.mpr
  intro P
  have hmem : n ∈ ( (g⁻¹ • P : Sylow p G) : Subgroup G) :=
    (Subgroup.mem_iInf.mp hn) (g⁻¹ • P)
  -- extract y
  change n ∈ (g⁻¹ • P : Sylow p G) at hmem
  -- rewrite
  change n ∈ (MulAut.conj (g⁻¹) • (P : Set G)) at hmem
  rw [Set.mem_smul_set] at hmem
  rcases hmem with ⟨y, hyP, hy⟩
  -- hy : _ • y = n
  change (MulAut.conj (g⁻¹)) y = n at hy
  change g * n * g⁻¹ ∈ P
  -- substitute n
  rw [← hy]
  -- goal simplify
  simp [mul_assoc]
  exact hyP
lemma sylow_iInf_isPGroup {G : Type*} [Group G] (p : ℕ) :
  IsPGroup p ((⨅ P : Sylow p G, (P : Subgroup G)) : Subgroup G) := by
  let P0 : Sylow p G := Classical.choice (Sylow.nonempty)
  have hle : (⨅ P : Sylow p G, (P : Subgroup G)) ≤ (P0 : Subgroup G) := iInf_le (fun P : Sylow p G => (P : Subgroup G)) P0
  exact IsPGroup.to_le P0.isPGroup' hle

lemma mem_sup_core_iff_mem_all_sylow {G : Type*} [Group G] (p : ℕ) (x:G) :
  x ∈ (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} : Subgroup G) ↔
    ∀ P : Sylow p G, x ∈ P := by
  let C : Subgroup G := sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}
  have Cn : C.Normal := sup_core_normal p
  letI : C.Normal := Cn
  have Cp : IsPGroup p C := sup_core_isPGroup p
  constructor
  · intro hx P
    apply Cp.le_sylow_of_normal P
    simpa [C] using hx
  · intro hx
    let T : Subgroup G := ⨅ P : Sylow p G, (P : Subgroup G)
    have Tn : T.Normal := sylow_iInf_normal p
    letI : T.Normal := Tn
    have Tp : IsPGroup p T := sylow_iInf_isPGroup p
    have hle : T ≤ C := by
      apply le_sSup
      exact ⟨Tn, Tp⟩
    apply hle
    exact Subgroup.mem_iInf.mpr hx
end Foo
namespace Foo
lemma pair_hyp_all_conjugate_pairs {G : Type*} [Group G] {p : ℕ} (x : G)
    (h : ∀ g : G, IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (a b : G) :
    IsPGroup p (Subgroup.closure
      ({a * x * a⁻¹, b * x * b⁻¹} : Set G)) := by
  have h0 := h (a⁻¹ * b)
  have h1 := IsPGroup.map h0 ((MulAut.conj a).toMonoidHom)
  rw [MonoidHom.map_closure] at h1
  -- image of pair
  -- simp only? try show sets equal
  have hset :
      ((MulAut.conj a).toMonoidHom '' ({x, (a⁻¹ * b) * x * (a⁻¹ * b)⁻¹} : Set G))
      = ({a * x * a⁻¹, b * x * b⁻¹} : Set G) := by
      -- map pair
      simp only [Set.image_insert_eq, Set.image_singleton]
      congr 2
      -- compare second expression
      -- `simp`?
      --#check
      simp [mul_assoc]
  rw [hset] at h1
  exact h1
end Foo
namespace Foo
lemma pair_hyp_singleton_isPGroup {G : Type*} [Group G] {p : ℕ} (x : G)
    (h : ∀ g : G, IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    IsPGroup p (Subgroup.closure ({x} : Set G)) := by
  have hset : ({x, (1:G)*x*(1:G)⁻¹} : Set G) = ({x}:Set G) := by simp
  have hx := h (1:G)
  rw [hset] at hx
  exact hx
end Foo
namespace Foo
lemma pair_hyp_mem_sylow_of_mem_normalizer {G : Type*} [Group G] {p : ℕ}
    (x : G)
    (h : ∀ g : G, IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (P : Sylow p G) (hxnorm : x ∈ Subgroup.normalizer (P : Subgroup G)) :
    x ∈ P := by
  -- H = closure of x, a p-subgroup inside normalizer
  let H : Subgroup G := Subgroup.closure ({x}:Set G)
  have Hp : IsPGroup p H := pair_hyp_singleton_isPGroup x h
  have HP_le : H ≤ Subgroup.normalizer (P : Subgroup G) := by
    apply (Subgroup.closure_le _).2
    intro y hy
    have hy' : y = x := by simpa using hy
    simpa [hy'] using hxnorm
  have hsup : IsPGroup p ((H ⊔ (P : Subgroup G)) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' Hp P.isPGroup' HP_le
  have hEq : H ⊔ (P : Subgroup G) = (P : Subgroup G) :=
    Eq.trans (P.is_maximal' hsup le_sup_right) rfl
  -- from x∈H infer x∈P
  have hxH : x ∈ H := by
    apply Subgroup.subset_closure
    simp
  have hxU : x ∈ (H ⊔ (P : Subgroup G)) := (show H ≤ (H ⊔ (P : Subgroup G) : Subgroup G) from le_sup_left) hxH
  rw [hEq] at hxU
  exact hxU
end Foo
namespace Foo
lemma pair_hyp_smul_eq_self_iff_mem {G : Type*} [Group G] {p : ℕ}
    (x : G)
    (h : ∀ g : G, IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (P : Sylow p G) :
    x • P = P ↔ x ∈ P := by
  rw [Sylow.smul_eq_iff_mem_normalizer]
  constructor
  · intro hn
    exact pair_hyp_mem_sylow_of_mem_normalizer x h P hn
  · intro hxmem
    exact (Subgroup.le_normalizer hxmem)
end Foo
namespace Foo
lemma restrict_pair_hyp_to_subgroup {G : Type*} [Group G] {p : ℕ}
    {H : Subgroup G} {x : G} (hx : x ∈ H)
    (hyp : ∀ g : G,
      IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    ∀ gh : H,
      IsPGroup p (Subgroup.closure ({(⟨x,hx⟩ : H), gh * ⟨x,hx⟩ * gh⁻¹} : Set H)) := by
  intro gh
  -- ambient K
  let K : Subgroup G := Subgroup.closure ({x, (gh:G) * x * (gh:G)⁻¹} : Set G)
  have Kp : IsPGroup p K := hyp (gh : G)
  let L : Subgroup H := Subgroup.closure
     ({(⟨x,hx⟩ : H), gh * ⟨x,hx⟩ * gh⁻¹} : Set H)
  suffices IsPGroup p L by exact this
  -- any element of closure L maps into closure K
  have hle : L ≤ K.comap H.subtype := by
     apply (Subgroup.closure_le _).2
     intro y hy
     have hy' : y = (⟨x,hx⟩:H) ∨ y = gh * ⟨x,hx⟩ * gh⁻¹ := by simpa using hy
     rcases hy' with h | h
     · -- goal after substitution
       change (y:G) ∈ K
       rw [h]
       change x ∈ Subgroup.closure ({x, (gh:G) * x * (gh:G)⁻¹} : Set G)
       apply Subgroup.subset_closure
       simp
     · change (y:G) ∈ K
       rw [h]
       change (gh:G) * x * (gh:G)⁻¹ ∈ K
       apply Subgroup.subset_closure
       simp
  -- define embedding of L into K
  let f : L →* K :=
    { toFun := fun y => ⟨((y.1:H):G), hle y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := by
        intro a b
        apply Subtype.ext
        change ((((a * b : L) : H):G)) = ((((a:L): H) : G)) * ((((b:L):H):G))
        simp }
  exact IsPGroup.of_injective Kp f (fun a b hab => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : K => (y:G)) hab)
end Foo
namespace Foo
lemma descend_pair_hyp_to_quotient {G : Type*} [Group G] {p : ℕ}
    {N : Subgroup G} [N.Normal] (x : G)
    (hyp : ∀ g : G,
      IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    ∀ g' : G ⧸ N,
       IsPGroup p (Subgroup.closure
          ({(x:G ⧸ N), g' * (x:G ⧸ N) * g'⁻¹} : Set (G ⧸ N))) := by
  intro g'
  rcases (QuotientGroup.mk'_surjective N g') with ⟨g, rfl⟩
  have hp := IsPGroup.map (hyp g) (QuotientGroup.mk' N)
  rw [MonoidHom.map_closure] at hp
  have hset :
    ((QuotientGroup.mk' N : G →* G ⧸ N) '' ({x, g*x*g⁻¹} : Set G)) =
      ({(x:G ⧸ N), ((g:G ⧸ N)) * (x:G ⧸ N) * ((g:G ⧸ N))⁻¹} : Set (G ⧸ N)) := by
    simp only [Set.image_insert_eq, Set.image_singleton]
    -- should map
    rw [map_mul, map_mul, map_inv]
    simp
  rw [hset] at hp
  rw [QuotientGroup.mk'_apply] -- rewrite g wrapper in goal
  change IsPGroup p (Subgroup.closure ({(x:G ⧸ N), ((g:G ⧸ N) * (x:G ⧸ N) * (g:G ⧸ N)⁻¹)} : Set (G ⧸ N)))
  exact hp
end Foo
namespace Foo
lemma pair_hyp_mem_sup_core_of_mem_center {G : Type*} [Group G]
    {p:ℕ} {x:G}
    (hyp : ∀ g : G,
      IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (hx : x ∈ Subgroup.center G) :
    x ∈ (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} : Subgroup G) := by
  let H : Subgroup G := Subgroup.closure ({x}:Set G)
  have Hle : H ≤ Subgroup.center G := by
    apply (Subgroup.closure_le _).2
    intro y hy
    have hyeq : y = x := by simpa using hy
    simpa [hyeq] using hx
  have Hn : H.Normal := by
    constructor
    intro n hn g
    have hn' : n ∈ Subgroup.center G := Hle hn
    have hc : g * n = n * g := (Subgroup.mem_center_iff.mp hn') g
    change g * n * g⁻¹ ∈ H
    rw [hc]
    simpa [mul_assoc] using hn
  have Hp : IsPGroup p H := pair_hyp_singleton_isPGroup x hyp
  have hsub : H ≤ (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} : Subgroup G) := by
    apply le_sSup
    exact ⟨Hn, Hp⟩
  apply hsub
  apply Subgroup.subset_closure
  simp
end Foo

namespace Foo
/-- Lifting membership in the largest normal p-subgroup across a normal
    p-kernel.  This is a useful completely elementary reduction in the
    difficult direction of Baer--Suzuki.  Notice that no finiteness is used
    here. -/
lemma mem_sup_core_of_quotient {G : Type*} [Group G] (p : ℕ)
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p N) (x : G)
    (hx : (x : G ⧸ N) ∈
      (sSup {Q : Subgroup (G ⧸ N) | Q.Normal ∧ IsPGroup p Q} : Subgroup (G ⧸ N))) :
    x ∈ (sSup {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q} : Subgroup G) := by
  let Cq : Subgroup (G ⧸ N) :=
    (sSup {Q : Subgroup (G ⧸ N) | Q.Normal ∧ IsPGroup p Q} : Subgroup (G ⧸ N))
  have Cqn : Cq.Normal := sup_core_normal p
  letI : Cq.Normal := Cqn
  have Cqp : IsPGroup p Cq := sup_core_isPGroup p
  let M : Subgroup G := Cq.comap (QuotientGroup.mk' N)
  have Mn : M.Normal := Subgroup.normal_comap (QuotientGroup.mk' N)
  have hker : IsPGroup p (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    exact hN
  have Mp : IsPGroup p M := Cqp.comap_of_ker_isPGroup (QuotientGroup.mk' N) hker
  have hle : M ≤ (sSup {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q} : Subgroup G) := by
    apply le_sSup
    exact ⟨Mn, Mp⟩
  apply hle
  change (QuotientGroup.mk' N) x ∈ Cq
  simpa [Cq, QuotientGroup.mk'_apply] using hx
end Foo

namespace Foo
/-- A quick consequence used to dispose of the soluble edge cases: when a
    Sylow subgroup is normal every p-element belongs to the p-core. -/
lemma pair_hyp_mem_sup_core_of_normal_sylow {G : Type*} [Group G]
    {p : ℕ} (x : G)
    (h : ∀ g : G, IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (P : Sylow p G) [nP : (P : Subgroup G).Normal] :
    x ∈ (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} : Subgroup G) := by
  have hpC : (P : Subgroup G) ≤
      (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} : Subgroup G) := by
    apply le_sSup
    exact ⟨nP, P.isPGroup'⟩
  have hxP : x ∈ P := by
    rcases pair_exists_sylow x x (h x) with ⟨Q,hx,_⟩
    have hle' : (P : Subgroup G) ≤ (Q : Subgroup G) := P.isPGroup'.le_sylow_of_normal Q
    have heq : (Q : Subgroup G) = (P : Subgroup G) :=
      P.is_maximal' Q.isPGroup' hle'
    change x ∈ (P : Subgroup G)
    rw [← heq]
    exact hx
  exact hpC hxP
end Foo

namespace Foo
/-- Conjugation restricts to an automorphism of a normal subgroup.  Keeping the
    explicit formula is handy for avoiding coercion headaches with the several
    conjugation actions. -/
noncomputable def conjOnNormal {G : Type*} [Group G] (H : Subgroup G)
    (hn : H.Normal) (g : G) : H ≃* H where
  toFun h := ⟨g * (h : G) * g⁻¹, hn.conj_mem h.1 h.2 g⟩
  invFun h := ⟨g⁻¹ * (h : G) * (g⁻¹)⁻¹, hn.conj_mem h.1 h.2 g⁻¹⟩
  left_inv h := by
    apply Subtype.ext
    change g⁻¹ * (g * (h:G) * g⁻¹) * (g⁻¹)⁻¹ = (h:G)
    simp [mul_assoc]
  right_inv h := by
    apply Subtype.ext
    change g * (g⁻¹ * (h:G) * (g⁻¹)⁻¹) * g⁻¹ = (h:G)
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    change g * ((a:G) * (b:G)) * g⁻¹ =
      (g * (a:G) * g⁻¹) * (g * (b:G) * g⁻¹)
    simp [mul_assoc]

@[simp]
lemma coe_conjOnNormal {G : Type*} [Group G] (H : Subgroup G)
    (hn : H.Normal) (g : G) (h : H) :
    ((conjOnNormal H hn g h : H) : G) = g * (h:G) * g⁻¹ := rfl

/-- The image in `G` of the p-core of a normal subgroup is again normal in
    `G`.  This characteristicity observation is often useful in the minimal
    counterexample reduction for Baer--Suzuki. -/
lemma map_sup_core_of_normal_normal {G : Type*} [Group G] (p : ℕ)
    (H : Subgroup G) (hn : H.Normal) :
    (Subgroup.map H.subtype
      (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H)).Normal := by
  let K : Subgroup H :=
    (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H)
  have kn : K.Normal := sup_core_normal p
  letI : K.Normal := kn
  have kp : IsPGroup p K := sup_core_isPGroup p
  -- automorphisms of `H` preserve its largest normal p-subgroup.
  have hchar : ∀ f : H ≃* H, K.map f.toMonoidHom ≤ K := by
    intro f
    have mn : (K.map f.toMonoidHom).Normal := kn.map f.toMonoidHom f.surjective
    have mp : IsPGroup p (K.map f.toMonoidHom) :=
      IsPGroup.map kp f.toMonoidHom
    apply le_sSup
    exact ⟨mn, mp⟩
  change (K.map H.subtype).Normal
  constructor
  intro n hnmem g
  rcases hnmem with ⟨h, hh, heq⟩
  -- `h` is an element of `H`.  Conjugate it by the automorphism above.
  let f : H ≃* H := conjOnNormal H hn g
  have hfh : f h ∈ K := by
    apply hchar f
    exact ⟨h, hh, rfl⟩
  -- and regard it again as an element of the image in `G`.
  refine ⟨f h, hfh, ?_⟩
  change g * (h:G) * g⁻¹ = g * n * g⁻¹
  -- `heq` is the equality coming from membership in a mapped subgroup.
  change (h:G) = n at heq
  rw [heq]
end Foo

namespace Foo
lemma mem_sup_core_of_normal_subgroup {G : Type*} [Group G] (p : ℕ)
    (H : Subgroup G) (hn : H.Normal) (x : G) (hx : x ∈ H)
    (hxH : (⟨x,hx⟩ : H) ∈
       (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H)) :
    x ∈ (sSup {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q} : Subgroup G) := by
  let K : Subgroup H :=
       (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H)
  have kp : IsPGroup p K := sup_core_isPGroup p
  let L : Subgroup G := K.map H.subtype
  have ln : L.Normal := map_sup_core_of_normal_normal p H hn
  have lp : IsPGroup p L := IsPGroup.map kp H.subtype
  have leC : L ≤
      (sSup {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q} : Subgroup G) := by
    apply le_sSup
    exact ⟨ln, lp⟩
  apply leC
  change x ∈ K.map H.subtype
  refine ⟨⟨x,hx⟩, ?_, rfl⟩
  simpa [K] using hxH
end Foo

namespace Foo
/-- Reformulation of the hypothesis in terms of Sylow subgroups.  The
    reverse implication is occasionally a more convenient way to use it:
    once a Sylow containing the pair is specified, the closure is a subgroup
    of that Sylow. -/
lemma pair_hyp_iff_sylow_pair {G : Type*} [Group G] {p : ℕ} (x : G) :
    (∀ g : G, IsPGroup p
       (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) ↔
    ∀ g : G, ∃ P : Sylow p G, x ∈ P ∧ g * x * g⁻¹ ∈ P := by
  constructor
  · intro h g
    exact pair_exists_sylow x g (h g)
  · intro h g
    rcases h g with ⟨P,hx,hgx⟩
    apply IsPGroup.to_le P.isPGroup'
    apply (Subgroup.closure_le (P : Subgroup G)).2
    intro y hy
    have h' : y = x ∨ y = g * x * g⁻¹ := by simpa using hy
    rcases h' with rfl | rfl
    · exact hx
    · exact hgx
end Foo

namespace Foo
/-- If `x` satisfies the pair hypothesis, the conjugation action of its cyclic
    subgroup on the Sylow subgroups has as fixed points precisely the Sylows
    containing `x`.  Consequently the usual fixed-point congruence for a
    p-group action is a congruence with that concrete subtype on the right. -/
lemma pair_hyp_card_sylow_modEq_mem {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (x : G)
    (h : ∀ g : G, IsPGroup p
       (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    Nat.card (Sylow p G) ≡
      Nat.card {P : Sylow p G // x ∈ (P : Subgroup G)} [MOD p] := by
  classical
  -- For a finite group every Sylow has finite index, hence the type of
  -- Sylows is finite.  Isolating this instance keeps the argument an ordinary
  -- `Nat.card` congruence.
  let P0 : Sylow p G := Classical.choice (Sylow.nonempty)
  letI : Finite (Sylow p G) := P0.finite_of_finiteIndex
  let H : Subgroup G := Subgroup.closure ({x} : Set G)
  have hHp : IsPGroup p H := pair_hyp_singleton_isPGroup x h
  have hmod := hHp.card_modEq_card_fixedPoints (Sylow p G)
  -- The fixed point lemma in `Sylow.lean` recognises a fixed Sylow as one
  -- containing the acting p-subgroup.  For `H = closure {x}` that is just
  -- membership of `x`.
  have hlev (P : Sylow p G) :
      H ≤ (P : Subgroup G) ↔ x ∈ (P : Subgroup G) := by
    constructor
    · intro hHP
      apply hHP
      change x ∈ Subgroup.closure ({x} : Set G)
      apply Subgroup.subset_closure
      simp
    · intro hxP
      change Subgroup.closure ({x} : Set G) ≤ (P : Subgroup G)
      apply (Subgroup.closure_le _).2
      intro y hy
      have hyx : y = x := by simpa using hy
      rw [hyx]
      exact hxP
  have hfix (P : Sylow p G) :
      P ∈ MulAction.fixedPoints H (Sylow p G) ↔
        x ∈ (P : Subgroup G) := by
    rw [hHp.sylow_mem_fixedPoints_iff]
    exact hlev P
  let e : (MulAction.fixedPoints H (Sylow p G)) ≃
          {P : Sylow p G // x ∈ (P : Subgroup G)} :=
    Equiv.subtypeEquiv (Equiv.refl (Sylow p G)) (by
      intro P
      simpa using (hfix P))
  have hc : Nat.card (MulAction.fixedPoints H (Sylow p G)) =
          Nat.card {P : Sylow p G // x ∈ (P : Subgroup G)} :=
    Nat.card_congr e
  simpa [hc] using hmod
end Foo

end
-- END INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/Forward.lean

-- BEGIN INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/Intersections.lean
section
open scoped Pointwise
namespace Foo
lemma map_conj_inf_subgroup {G : Type*} [Group G] (c : G)
    (H K : Subgroup G) :
    (H ⊓ K).map (MulAut.conj c : G ≃* G).toMonoidHom =
      ((MulAut.conj c) • H ⊓ (MulAut.conj c) • K : Subgroup G) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj c : G ≃* G).injective]
  rfl

def subgroupInfConjMulEquiv {G : Type*} [Group G] (c : G)
    (H K : Subgroup G) :
    (H ⊓ K : Subgroup G) ≃*
      ((MulAut.conj c) • H ⊓ (MulAut.conj c) • K : Subgroup G) := by
  let I : Subgroup G := H ⊓ K
  let J : Subgroup G := (MulAut.conj c) • H ⊓ (MulAut.conj c) • K
  have h : I.map (MulAut.conj c : G ≃* G).toMonoidHom = J := by
    simpa [I, J] using map_conj_inf_subgroup c H K
  exact ((MulAut.conj c : G ≃* G).subgroupMap I).trans (MulEquiv.subgroupCongr h)

lemma natCard_subgroupInf_smul {G : Type*} [Group G] [Finite G]
    (c : G) (H K : Subgroup G) :
    Nat.card (H ⊓ K : Subgroup G) =
      Nat.card ((MulAut.conj c) • H ⊓ (MulAut.conj c) • K : Subgroup G) :=
  Nat.card_congr (subgroupInfConjMulEquiv c H K).toEquiv

lemma map_conj_sylow_inf {G : Type*} [Group G]
    {p : ℕ} (c : G) (R Q : Sylow p G) :
    ((R : Subgroup G) ⊓ (Q : Subgroup G)).map (MulAut.conj c : G ≃* G).toMonoidHom =
      (((c • R : Sylow p G) : Subgroup G) ⊓
        ((c • Q : Sylow p G) : Subgroup G) : Subgroup G) := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj c : G ≃* G).injective]
  change _ = (MulAut.conj c) • (R : Subgroup G) ⊓
    (MulAut.conj c) • (Q : Subgroup G)
  rfl

def sylowInfConjMulEquiv {G : Type*} [Group G]
    {p : ℕ} (c : G) (R Q : Sylow p G) :
    ((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) ≃*
      (((c • R : Sylow p G) : Subgroup G) ⊓
        ((c • Q : Sylow p G) : Subgroup G) : Subgroup G) := by
  let I : Subgroup G := (R : Subgroup G) ⊓ (Q : Subgroup G)
  let J : Subgroup G := ((c • R : Sylow p G) : Subgroup G) ⊓
    ((c • Q : Sylow p G) : Subgroup G)
  have h : I.map (MulAut.conj c : G ≃* G).toMonoidHom = J := by
    simpa [I, J] using map_conj_sylow_inf c R Q
  exact ((MulAut.conj c : G ≃* G).subgroupMap I).trans (MulEquiv.subgroupCongr h)

lemma natCard_sylowInf_smul {G : Type*} [Group G] [Finite G]
    {p : ℕ} (c : G) (R Q : Sylow p G) :
    Nat.card ((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) =
      Nat.card (((c • R : Sylow p G) : Subgroup G) ⊓
        ((c • Q : Sylow p G) : Subgroup G) : Subgroup G) :=
  Nat.card_congr (sylowInfConjMulEquiv c R Q).toEquiv
end Foo

end
-- END INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/Intersections.lean

-- BEGIN INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/MaxWitness.lean
section

/-!
A finite search lemma for the difficult Baer--Suzuki branch.  For a chosen
Sylow `Q`, a *pair witness* is a Sylow `R` containing `x` and one conjugate
`a*x*a⁻¹`, where the latter also lies in `Q`.  Such witnesses form a
nonempty finite type: one first chooses a Sylow containing `x`, conjugates it
to `Q`, and uses the pair hypothesis once more.  Consequently the size of
`R ⊓ Q` attains a maximum on witnesses.  This keeps the maximality invariant
explicit for the simultaneous-intersection argument downstream.
-/
namespace Foo

open scoped Pointwise

/-- The set of pair witnesses for a fixed Sylow `Q` may be chosen with
    maximal intersection with `Q`.

A witness consists of `a : G`, `R : Sylow p G`, `x ∈ R`, and
`a*x*a⁻¹ ∈ R ∩ Q`.  The conclusion selects such a pair for which the finite
cardinality of `R ⊓ Q` is greater than or equal to that of every other
witness.  The hypothesis `x ∉ Q` is part of the convenient interface for the
minimal-counterexample case, but is not needed in the finite maximization
argument itself.
-/
lemma pair_witness_max_intersection {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (x : G)
    (hyp : ∀ g : G,
      IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (Q : Sylow p G) (hxQ : x ∉ (Q : Subgroup G)) :
    ∃ (a : G) (R : Sylow p G),
      x ∈ (R : Subgroup G) ∧
      a * x * a⁻¹ ∈ (R : Subgroup G) ∧
      a * x * a⁻¹ ∈ (Q : Subgroup G) ∧
      ∀ (b : G) (S : Sylow p G),
        x ∈ (S : Subgroup G) →
        b * x * b⁻¹ ∈ (S : Subgroup G) →
        b * x * b⁻¹ ∈ (Q : Subgroup G) →
          Nat.card (↥((S : Subgroup G) ⊓ (Q : Subgroup G))) ≤
            Nat.card (↥((R : Subgroup G) ⊓ (Q : Subgroup G))) := by
  classical
  have _hx_unused := hxQ -- kept in the interface for the minimal-counterexample branch
  -- In a finite group every Sylow has finite index, so there are finitely
  -- many Sylow subgroups.  Keeping this local instance avoids any decidable
  -- packaging in the witness statement.
  let P₀ : Sylow p G := Classical.choice (Sylow.nonempty)
  letI : Finite (Sylow p G) := P₀.finite_of_finiteIndex
  -- Package `(a,R)` as a finite subtype.  Products of finite types and their
  -- subtypes are finite; membership does not need to be decidable here.
  let Witness : Type _ :=
    { w : G × Sylow p G //
        x ∈ (w.2 : Subgroup G) ∧
        w.1 * x * w.1⁻¹ ∈ (w.2 : Subgroup G) ∧
        w.1 * x * w.1⁻¹ ∈ (Q : Subgroup G) }
  have hnonempty : Nonempty Witness := by
    -- Start with a Sylow containing `x` using the pair at `g = 1`.
    rcases pair_exists_sylow x (1 : G) (hyp 1) with
      ⟨P, hxP, _⟩
    -- All Sylows of a finite group (for a prime `p`) are conjugate, hence
    -- some conjugate of that first Sylow is the fixed `Q`.
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G P Q
    have hyQ : a * x * a⁻¹ ∈ (Q : Subgroup G) := by
      rw [← ha]
      change a * x * a⁻¹ ∈ (MulAut.conj a • (P : Set G))
      rw [Set.mem_smul_set]
      exact ⟨x, hxP, rfl⟩
    -- Apply the pair hypothesis at this `a` to get a Sylow containing both
    -- elements; together with `hyQ` it is a witness.
    rcases pair_exists_sylow x a (hyp a) with
      ⟨R, hxR, hyR⟩
    exact ⟨⟨(a, R), hxR, hyR, hyQ⟩⟩
  -- Finite products and their subtypes inherit `Finite`; invoke the general
  -- maximum principle on the natural-valued function `R ↦ card (R ⊓ Q)`.
  letI : Nonempty Witness := hnonempty
  have hmax :
      ∃ w₀ : Witness,
        ∀ w : Witness,
          (fun z : Witness =>
              Nat.card (↥(((z.1.2 : Sylow p G) : Subgroup G) ⊓ (Q : Subgroup G)))) w ≤
            (fun z : Witness =>
              Nat.card (↥(((z.1.2 : Sylow p G) : Subgroup G) ⊓ (Q : Subgroup G)))) w₀ :=
    Finite.exists_max (fun z : Witness =>
      Nat.card (↥(((z.1.2 : Sylow p G) : Subgroup G) ⊓ (Q : Subgroup G))))
  rcases hmax with ⟨w₀, hw₀⟩
  rcases w₀ with ⟨⟨a, R⟩, hxR, hyR, hyQ⟩
  refine ⟨a, R, hxR, hyR, hyQ, ?_⟩
  intro b S hxS hyS hyQS
  -- Build any rival witness and apply maximality.
  simpa using
    (hw₀ (⟨(b, S), hxS, hyS, hyQS⟩ : Witness))

end Foo

end
-- END INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/MaxWitness.lean

-- BEGIN INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/Reductions.lean
section

namespace Foo
open scoped Classical

/-- In a minimal-counterexample argument one knows that `x` belongs to the
`p`-core of each proper overgroup of `x`.  The same is true for a conjugate
(worker lemma `conj_mem_sup_core_of_hproper`).  In particular, if the
normalizer of a Sylow subgroup is proper, every conjugate of `x` which
normalizes that Sylow already belongs to it.  This assertion uses *only* the
minimality assertion `hproper`; it doesn't need the Baer--Suzuki pair
hypothesis again. -/
lemma conj_mem_sylow_of_mem_normalizer_of_hproper
    {G : Type*} [Group G] {p : ℕ} {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x, hxH⟩ : H) ∈
        (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H))
    (P : Sylow p G)
    (hNP : Subgroup.normalizer (P : Set G) ≠ ⊤)
    (g : G) (hy : g * x * g⁻¹ ∈ Subgroup.normalizer (P : Set G)) :
    g * x * g⁻¹ ∈ (P : Subgroup G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  have hn : N ≠ (⊤ : Subgroup G) := by
    simpa [N] using hNP
  have hyN : g * x * g⁻¹ ∈ N := by simpa [N] using hy
  -- minimality, transported by conjugation
  have hcore : (⟨g * x * g⁻¹, hyN⟩ : N) ∈
        (sSup {Q : Subgroup N | Q.Normal ∧ IsPGroup p Q} : Subgroup N) :=
    conj_mem_sup_core_of_hproper hproper g N hyN hn
  -- A Sylow subgroup of `G` remains Sylow on restriction to an overgroup;
  -- use that particular Sylow in the intersection-of-Sylows description of
  -- the `p`-core inside `N`.
  have hle : (P : Subgroup G) ≤ N := by
    change (P : Subgroup G) ≤ Subgroup.normalizer (P : Set G)
    exact Subgroup.le_normalizer
  have hh : (⟨g * x * g⁻¹, hyN⟩ : N) ∈
       (P.subtype hle : Sylow p N) := by
    apply (mem_sup_core_iff_mem_all_sylow p
      (⟨g * x * g⁻¹, hyN⟩ : N)).1 hcore
  exact hh

/-- The preceding obstruction in terms of a set of conjugates: in a proper
normalizer no conjugate of `x` occurs outside the Sylow. This formulation is
often convenient under a set-builder. -/
lemma conj_class_inter_normalizer_subset
    {G : Type*} [Group G] {p : ℕ} {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x, hxH⟩ : H) ∈
        (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H))
    (P : Sylow p G) (hNP : Subgroup.normalizer (P : Set G) ≠ ⊤) :
    {y : G | ∃ g : G, y = g * x * g⁻¹} ∩
        (Subgroup.normalizer (P : Set G) : Set G)
      ⊆ (P : Set G) := by
  intro y hy
  rcases hy.1 with ⟨g, rfl⟩
  have := conj_mem_sylow_of_mem_normalizer_of_hproper
      hproper P hNP g hy.2
  exact this

/-- More generally, in *any* proper subgroup all conjugates of the
minimal-counterexample element that it happens to contain lie in its own
`p`-core.  Notice that this doesn't assert the subgroup is generated by
conjugates.  It's safe to use in the closure form below. -/
lemma conj_in_proper_overgroup_mem_core
    {G : Type*} [Group G] {p : ℕ} {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x, hxH⟩ : H) ∈
        (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H))
    (T : Subgroup G) (hT : T ≠ ⊤)
    {y : G} (hyclass : ∃ g : G, y = g * x * g⁻¹) (hyT : y ∈ T) :
    (⟨y, hyT⟩ : T) ∈
      (sSup {Q : Subgroup T | Q.Normal ∧ IsPGroup p Q} : Subgroup T) := by
  rcases hyclass with ⟨g, rfl⟩
  exact conj_mem_sup_core_of_hproper hproper g T hyT hT

/-- The closure *inside a proper overgroup* of the conjugates it contains is
bounded by its `p`-core.  This packages the pointwise minimality assertion in
an order-theoretic form; in particular that closure is a `p`-group.

We use the natural subset of the subgroup type.  Writing it this way avoids
claims about conjugates that need not lie in the chosen subgroup. -/
lemma closure_conj_in_proper_le_core
    {G : Type*} [Group G] {p : ℕ} {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x, hxH⟩ : H) ∈
        (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H))
    (T : Subgroup G) (hT : T ≠ ⊤) :
    Subgroup.closure
        ({t : T | ∃ g : G, (t : G) = g * x * g⁻¹} : Set T)
      ≤ (sSup {Q : Subgroup T | Q.Normal ∧ IsPGroup p Q} : Subgroup T) := by
  apply (Subgroup.closure_le _).2
  intro t ht
  have ht' : ∃ g : G, (t : G) = g * x * g⁻¹ := ht
  exact conj_in_proper_overgroup_mem_core hproper T hT ht'
    (t.property)

lemma closure_conj_in_proper_isPGroup
    {G : Type*} [Group G] {p : ℕ} {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x, hxH⟩ : H) ∈
        (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H))
    (T : Subgroup G) (hT : T ≠ ⊤) :
    IsPGroup p
      (Subgroup.closure
        ({t : T | ∃ g : G, (t : G) = g * x * g⁻¹} : Set T)) := by
  apply IsPGroup.to_le (sup_core_isPGroup (G := T) p)
  exact closure_conj_in_proper_le_core hproper T hT

/-- A particularly useful specialisation: if the normalizer of a Sylow is
proper, the closure in its subgroup type of all conjugates there embeds in the
Sylow itself.  Later counting/local arguments only have to find one
conjugate in the normalizer and outside the Sylow. -/
lemma closure_conj_in_normalizer_le_sylow
    {G : Type*} [Group G] {p : ℕ} {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x, hxH⟩ : H) ∈
        (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H))
    (P : Sylow p G)
    (hNP : Subgroup.normalizer (P : Set G) ≠ ⊤) :
    Subgroup.closure
      ({t : Subgroup.normalizer (P : Set G) |
        ∃ g : G, (t : G) = g * x * g⁻¹} :
        Set (Subgroup.normalizer (P : Set G)))
      ≤ (P.subtype (by exact Subgroup.le_normalizer) :
          Subgroup (Subgroup.normalizer (P : Set G))) := by
  apply (Subgroup.closure_le _).2
  intro t ht
  rcases ht with ⟨g, heq⟩
  change (t : G) ∈ (P : Subgroup G)
  rw [heq]
  exact conj_mem_sylow_of_mem_normalizer_of_hproper
    hproper P hNP g (by
      -- this is exactly the property of an element of the normalizer type
      rw [← heq]
      exact t.property)


/-- The elementary normalizer condition in a Sylow.  For a proper subgroup
`I` of a finite Sylow `P` there is an element of `P\I` normalizing `I`.
Although often used tacitly in the "maximal Sylow intersection" step, it is
not true for arbitrary overgroups; the point is that the group `P` is a
finite p-group, hence nilpotent.  This explicit ambient version is handy for
intersection arguments in `G`. -/
lemma exists_mem_sylow_normalizer_not_mem
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (I : Subgroup G)
    (hI : I ≤ (P : Subgroup G)) (hne : I ≠ (P : Subgroup G)) :
    ∃ z : G, z ∈ (P : Subgroup G) ∧
      z ∈ Subgroup.normalizer (I : Set G) ∧ z ∉ I := by
  classical
  let J : Subgroup P := I.subgroupOf (P : Subgroup G)
  have hJ : J ≠ (⊤ : Subgroup P) := by
    intro ht
    apply hne
    apply le_antisymm hI
    intro a haP
    let aP : P := ⟨a, haP⟩
    have haJ : aP ∈ J := by rw [ht]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp haJ)
  letI : Finite P := inferInstance
  letI : Group.IsNilpotent P := IsPGroup.isNilpotent P.isPGroup'
  have hlt : J < Subgroup.normalizer (J : Set P) :=
    (normalizerCondition_of_isNilpotent (G := P)) J (lt_top_iff_ne_top.mpr hJ)
  rcases SetLike.exists_of_lt hlt with ⟨z, hzN, hzout⟩
  -- regard `z : P` as an ambient element
  refine ⟨(z : G), z.property, ?_, ?_⟩
  · -- a normalizer in `P` is also an ambient normalizer of `I ≤ P`
    apply (Subgroup.mem_normalizer_iff).2
    intro a
    constructor
    · intro ha
      have haP : a ∈ (P : Subgroup G) := hI ha
      let aP : P := ⟨a, haP⟩
      have haJ : aP ∈ J := Subgroup.mem_subgroupOf.mpr ha
      have he := (Subgroup.mem_normalizer_iff.mp hzN aP).1 haJ
      -- membership in the subgroup-of is exactly ambient membership
      exact Subgroup.mem_subgroupOf.mp he
    · intro hza
      have hzP : (z : G)⁻¹ ∈ (P : Subgroup G) :=
        (P : Subgroup G).inv_mem z.property
      have hconP : (z : G) * a * (z : G)⁻¹ ∈
          (P : Subgroup G) := hI hza
      have haP : a ∈ (P : Subgroup G) := by
        have hm : (z : G)⁻¹ * ((z : G) * a * (z : G)⁻¹) *
                (z : G) ∈ (P : Subgroup G) :=
          (P : Subgroup G).mul_mem
            ((P : Subgroup G).mul_mem hzP hconP) z.property
        simpa [mul_assoc] using hm
      let aP : P := ⟨a, haP⟩
      have hconJ : z * aP * z⁻¹ ∈ J :=
        Subgroup.mem_subgroupOf.mpr hza
      have he := (Subgroup.mem_normalizer_iff.mp hzN aP).2 hconJ
      exact Subgroup.mem_subgroupOf.mp he
  · intro hzI
    apply hzout
    exact Subgroup.mem_subgroupOf.mpr hzI


/-- With trivial ambient `p`-core, a nontrivial conjugate cannot lie in a
normal `p`-subgroup. Equivalently the normalizer of any `p`-subgroup
containing that conjugate is a *proper* subgroup. This is the other small
ingredient in the usual Sylow-intersection reduction. -/
lemma normalizer_ne_top_of_conj_mem_of_core_eq_bot
    {G : Type*} [Group G] {p : ℕ} {x : G}
    (hc : (sSup {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q} : Subgroup G)
              = (⊥ : Subgroup G))
    (hx1 : x ≠ 1) (I : Subgroup G) (hIp : IsPGroup p I)
    (g : G) (hmem : g * x * g⁻¹ ∈ I) :
    Subgroup.normalizer (I : Set G) ≠ (⊤ : Subgroup G) := by
  classical
  intro htop
  have hn : I.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have hle : I ≤ (sSup {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q} : Subgroup G) := by
    apply le_sSup
    exact ⟨hn, hIp⟩
  have hbot : I = (⊥ : Subgroup G) := by
    apply bot_unique
    simpa [hc] using hle
  have hone : g * x * g⁻¹ = (1 : G) := by
    have : g * x * g⁻¹ ∈ (⊥ : Subgroup G) := by simpa [hbot] using hmem
    simpa using this
  apply hx1
  calc
    x = g⁻¹ * (g * x * g⁻¹) * g := by simp [mul_assoc]
    _ = 1 := by rw [hone]; simp

/-- Local form used at a Sylow intersection `I`: its normalizer is proper by
`normalizer_ne_top_of_conj_mem_of_core_eq_bot`; minimality puts the common
conjugate in the `p`-core of that normalizer, hence it lies in every Sylow *of
the normalizer*.  This should not be confused with lying in every Sylow of
`G`. -/
lemma conj_mem_all_sylow_of_normalizer
    {G : Type*} [Group G] {p : ℕ} {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x, hxH⟩ : H) ∈
        (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H))
    (I : Subgroup G)
    (hN : Subgroup.normalizer (I : Set G) ≠ (⊤ : Subgroup G))
    (g : G) (hy : g * x * g⁻¹ ∈ Subgroup.normalizer (I : Set G)) :
    ∀ U : Sylow p (Subgroup.normalizer (I : Set G)),
      (⟨g * x * g⁻¹, hy⟩ : Subgroup.normalizer (I : Set G)) ∈ U := by
  classical
  have hcore := conj_mem_sup_core_of_hproper hproper g
    (Subgroup.normalizer (I : Set G)) hy hN
  exact (mem_sup_core_iff_mem_all_sylow p _).1 hcore

/-- Combination convenient for two Sylows `P,R` sharing a nontrivial
conjugate in an intersection `I`: every Sylow of `N_G(I)` contains that
conjugate.  The next (non elementary) part of the Baer--Suzuki argument is to
turn this local information into increased Sylow intersection. -/
lemma conj_mem_all_sylow_of_normalizer_of_core_eq_bot
    {G : Type*} [Group G] {p : ℕ} {x : G}
    (hc : (sSup {Q : Subgroup G | Q.Normal ∧ IsPGroup p Q} : Subgroup G)
              = (⊥ : Subgroup G))
    (hx1 : x ≠ 1)
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x, hxH⟩ : H) ∈
        (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H))
    (I : Subgroup G) (hIp : IsPGroup p I)
    (g : G) (hmem : g * x * g⁻¹ ∈ I) :
    let hN : g * x * g⁻¹ ∈ Subgroup.normalizer (I : Set G) :=
        Subgroup.le_normalizer hmem
    ∀ U : Sylow p (Subgroup.normalizer (I : Set G)),
      (⟨g * x * g⁻¹, hN⟩ : Subgroup.normalizer (I : Set G)) ∈ U := by
  classical
  intro hN U
  exact conj_mem_all_sylow_of_normalizer hproper I
    (normalizer_ne_top_of_conj_mem_of_core_eq_bot hc hx1 I hIp g hmem)
    g hN U


/-- One side of the Sylow-intersection enlargement step.  Let `I ≤ R` be a
proper subgroup of a Sylow, put `N=N_G(I)`, and assume a particular element
`y∈I` occurs in *every* Sylow of `N` (as supplied by the preceding lemma in a
minimal counterexample).  Then one can extend a Sylow of `N` containing
`R∩N` to a Sylow `T` of `G`; it still contains `y`, and its intersection with
`R` is strictly larger than `I`.  The hard part later is synchronising this
construction for two different Sylows; this one-sided statement is often a
useful clean start.
-/
lemma exists_sylow_with_larger_intersection
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R : Sylow p G) (I : Subgroup G) (hI : I ≤ (R : Subgroup G))
    (hne : I ≠ (R : Subgroup G)) (y : G) (hyI : y ∈ I)
    (hall : ∀ U : Sylow p (Subgroup.normalizer (I : Set G)),
      (⟨y, Subgroup.le_normalizer hyI⟩ :
        Subgroup.normalizer (I : Set G)) ∈ U) :
    ∃ T : Sylow p G,
      y ∈ (T : Subgroup G) ∧ I < ((R : Subgroup G) ⊓ (T : Subgroup G)) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (I : Set G)
  -- The part of `R` in the normalizer is a p-subgroup of `N`.
  let A : Subgroup N := (R : Subgroup G).subgroupOf N
  have hAp : IsPGroup p A :=
    IsPGroup.comap_of_injective R.isPGroup' N.subtype
      (Subgroup.subtype_injective N)
  obtain ⟨U, hAU⟩ := hAp.exists_le_sylow
  -- extend it back to a Sylow of the ambient group
  have hUp : IsPGroup p (Subgroup.map N.subtype (U : Subgroup N)) :=
    IsPGroup.map U.isPGroup' N.subtype
  obtain ⟨T, hUT⟩ := hUp.exists_le_sylow
  refine ⟨T, ?_, ?_⟩
  · -- `y` is in this `U`, hence in its ambient extension `T`
    apply hUT
    have hyN : y ∈ N := Subgroup.le_normalizer hyI
    refine ⟨(⟨y, hyN⟩ : N), ?_, rfl⟩
    have h := hall U
    exact h
  · -- Every element of `I` is in `R ∩ T`.
    have hle : I ≤ ((R : Subgroup G) ⊓ (T : Subgroup G)) := by
      intro a ha
      refine ⟨hI ha, ?_⟩
      apply hUT
      have haN : a ∈ N := Subgroup.le_normalizer ha
      refine ⟨(⟨a, haN⟩ : N), ?_, rfl⟩
      apply hAU
      -- membership in `A=R.subgroupOf N` is ambient membership in `R`
      exact (Subgroup.mem_subgroupOf.mpr (hI ha))
    -- find an element of `R\I` normalizing `I`; it belongs to `A`, hence
    -- to `U` and `T`, and witnesses strictness.
    obtain ⟨z, hzR, hzN, hzout⟩ :=
      exists_mem_sylow_normalizer_not_mem R I hI hne
    have hzT : z ∈ (T : Subgroup G) := by
      apply hUT
      have hzN' : z ∈ N := hzN
      refine ⟨(⟨z, hzN'⟩ : N), ?_, rfl⟩
      apply hAU
      exact (Subgroup.mem_subgroupOf.mpr hzR)
    exact lt_of_le_not_ge hle (by
      intro hback
      exact hzout (hback ⟨hzR, hzT⟩))


/-- The easy terminal case of the two-sided intersection step.  If both
Sylows already lie in a *proper* normalizer, and one of them contains `x`,
then so does the other: minimality puts `x` in the core of the normalizer.
It is important to keep the two inclusions as hypotheses.  In an enlargement
argument the Sylows obtained by extending a Sylow of the normalizer need not
themselves be contained in it. -/
lemma mem_sylow_of_le_proper_overgroup
    {G : Type*} [Group G] {p : ℕ} {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x, hxH⟩ : H) ∈
        (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H))
    (R Q : Sylow p G) (hxR : x ∈ (R : Subgroup G))
    (N : Subgroup G) (hN : N ≠ ⊤)
    (hRN : (R : Subgroup G) ≤ N) (hQN : (Q : Subgroup G) ≤ N) :
    x ∈ (Q : Subgroup G) := by
  classical
  have hxN : x ∈ N := hRN hxR
  have hc := hproper N hxN hN
  have hm : (⟨x, hxN⟩ : N) ∈ (Q.subtype hQN : Sylow p N) :=
    (mem_sup_core_iff_mem_all_sylow p _).1 hc _
  exact hm

lemma mem_sylow_of_le_normalizer_of_hproper
    {G : Type*} [Group G] {p : ℕ} {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x, hxH⟩ : H) ∈
        (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H))
    (R Q : Sylow p G) (hxR : x ∈ (R : Subgroup G))
    (I : Subgroup G)
    (hN : Subgroup.normalizer (I : Set G) ≠ (⊤ : Subgroup G))
    (hRN : (R : Subgroup G) ≤ Subgroup.normalizer (I : Set G))
    (hQN : (Q : Subgroup G) ≤ Subgroup.normalizer (I : Set G)) :
    x ∈ (Q : Subgroup G) :=
  mem_sylow_of_le_proper_overgroup hproper R Q hxR
    (Subgroup.normalizer (I : Set G)) hN hRN hQN


/-- Conjugates which happen to lie in a subgroup are stable under
conjugation *in that subgroup*. Thus their closure in the subgroup type is
normal there. Combined with `closure_conj_in_proper_isPGroup` this identifies
the largest local subgroup generated by the class as a normal p-subgroup;
it avoids any choice of representatives for the conjugacy class. -/
lemma closure_conj_in_subgroup_normal
    {G : Type*} [Group G] (x : G) (T : Subgroup G) :
    (Subgroup.closure
      ({t : T | ∃ a : G, (t : G) = a * x * a⁻¹} : Set T)).Normal := by
  classical
  let S : Set T := {t : T | ∃ a : G, (t : G) = a * x * a⁻¹}
  let K : Subgroup T := Subgroup.closure S
  change K.Normal
  constructor
  intro n hn g
  -- induction in the generator while keeping the conjugating element `g`
  have Hind (z : T) (hz : z ∈ K) : g * z * g⁻¹ ∈ K := by
    change z ∈ Subgroup.closure S at hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
        apply Subgroup.subset_closure
        change ∃ a : G, ((g * z * g⁻¹ : T) : G) = a * x * a⁻¹
        rcases hz with ⟨a, ha⟩
        refine ⟨(g : G) * a, ?_⟩
        change (g : G) * (z : G) * (g : G)⁻¹ =
          ((g : G) * a) * x * ((g : G) * a)⁻¹
        rw [ha]
        simp [mul_assoc]
    | one => simp [K]
    | mul z w hz hw iz iw =>
        -- the generators' closure is a subgroup
        have hz' : g * z * g⁻¹ ∈ K := iz
        have hw' : g * w * g⁻¹ ∈ K := iw
        have hh : (g * z * g⁻¹) * (g * w * g⁻¹) ∈ K := K.mul_mem hz' hw'
        simpa [mul_assoc] using hh
    | inv z hz iz =>
        have hh : (g * z * g⁻¹)⁻¹ ∈ K := K.inv_mem iz
        simpa [mul_assoc] using hh
  exact Hind n hn


/-- Strengthening of the one-sided enlargement with an extra element of the
normalizer's core.  The proof is identical, but recording this element matters
for iterating an ``x-containing / x-omitting'' pair: any extension from the
normalizer still contains everything lying in every Sylow of it. -/
lemma exists_sylow_with_larger_intersection_two
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R : Sylow p G) (I : Subgroup G) (hI : I ≤ (R : Subgroup G))
    (hne : I ≠ (R : Subgroup G)) (y : G) (hyI : y ∈ I)
    (hall : ∀ U : Sylow p (Subgroup.normalizer (I : Set G)),
      (⟨y, Subgroup.le_normalizer hyI⟩ :
        Subgroup.normalizer (I : Set G)) ∈ U)
    (z : G) (hzN : z ∈ Subgroup.normalizer (I : Set G))
    (hallz : ∀ U : Sylow p (Subgroup.normalizer (I : Set G)),
      (⟨z, hzN⟩ : Subgroup.normalizer (I : Set G)) ∈ U) :
    ∃ T : Sylow p G,
      y ∈ (T : Subgroup G) ∧ z ∈ (T : Subgroup G) ∧
        I < ((R : Subgroup G) ⊓ (T : Subgroup G)) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (I : Set G)
  let A : Subgroup N := (R : Subgroup G).subgroupOf N
  have hAp : IsPGroup p A :=
    IsPGroup.comap_of_injective R.isPGroup' N.subtype
      (Subgroup.subtype_injective N)
  obtain ⟨U, hAU⟩ := hAp.exists_le_sylow
  have hUp : IsPGroup p (Subgroup.map N.subtype (U : Subgroup N)) :=
    IsPGroup.map U.isPGroup' N.subtype
  obtain ⟨T, hUT⟩ := hUp.exists_le_sylow
  refine ⟨T, ?_, ?_, ?_⟩
  · apply hUT
    refine ⟨(⟨y, Subgroup.le_normalizer hyI⟩ : N), ?_, rfl⟩
    exact hall U
  · apply hUT
    refine ⟨(⟨z, hzN⟩ : N), ?_, rfl⟩
    exact hallz U
  · have hle : I ≤ ((R : Subgroup G) ⊓ (T : Subgroup G)) := by
      intro a ha
      refine ⟨hI ha, ?_⟩
      apply hUT
      have haN : a ∈ N := Subgroup.le_normalizer ha
      refine ⟨(⟨a, haN⟩ : N), ?_, rfl⟩
      apply hAU
      exact (Subgroup.mem_subgroupOf.mpr (hI ha))
    obtain ⟨w, hwR, hwN, hwout⟩ :=
      exists_mem_sylow_normalizer_not_mem R I hI hne
    have hwT : w ∈ (T : Subgroup G) := by
      apply hUT
      have hwN' : w ∈ N := hwN
      refine ⟨(⟨w, hwN'⟩ : N), ?_, rfl⟩
      apply hAU
      exact (Subgroup.mem_subgroupOf.mpr hwR)
    exact lt_of_le_not_ge hle (by
      intro hh; exact hwout (hh ⟨hwR, hwT⟩))

end Foo

end
-- END INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/Reductions.lean

-- BEGIN INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/MaxBad.lean
section

/-! A slightly more flexible compactness reduction for the hard local step.
    The "omitting" Sylow is allowed to move.  All relevant data form a finite
    type.  Thus a bad pair, if one exists, has an intersection of maximum
    order among all bad pairs.  This is the useful replacement for choosing
    an arbitrary Sylow extension out of a normalizer. -/
namespace Foo
open scoped Pointwise

lemma natCard_subgroup_lt_of_lt {G : Type*} [Group G]
    {H K : Subgroup G} [Finite K] (h : H < K) : Nat.card H < Nat.card K := by
  classical
  let f : H → K := fun z => ⟨z, h.le z.property⟩
  letI : Finite H := Finite.of_injective f (by
    intro a b hab
    have hv : (a : G) = (b : G) := congrArg (fun t : K => (t : G)) hab
    exact Subtype.ext hv)
  -- using temporary Fintypes makes strictness of inclusion transparent
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype K := Fintype.ofFinite K
  have hs : (H : Set G) ⊂ (K : Set G) :=
    (Set.ssubset_iff_subset_ne).2 ⟨(SetLike.coe_subset_coe.mpr h.le), by
      intro hh
      apply h.ne
      exact SetLike.coe_injective hh⟩
  simpa [Nat.card_eq_fintype_card] using
    (Set.card_lt_card hs)

/-- In a counterexample an omitting Sylow can be varied as well as the
    common conjugate.  There is a bad triple which maximises `|R ∩ Q|`
    among all of them. -/
lemma bad_pair_max_intersection {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (x : G)
    (hyp : ∀ g : G,
      IsPGroup p (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (Q₀ : Sylow p G) (hm₀ : x ∉ (Q₀ : Subgroup G)) :
    ∃ (Q : Sylow p G) (a : G) (R : Sylow p G),
      x ∉ (Q : Subgroup G) ∧
      x ∈ (R : Subgroup G) ∧
      a * x * a⁻¹ ∈ (R : Subgroup G) ∧
      a * x * a⁻¹ ∈ (Q : Subgroup G) ∧
      ∀ (Q' : Sylow p G) (b : G) (S : Sylow p G),
        x ∉ (Q' : Subgroup G) →
        x ∈ (S : Subgroup G) →
        b * x * b⁻¹ ∈ (S : Subgroup G) →
        b * x * b⁻¹ ∈ (Q' : Subgroup G) →
          Nat.card (↥((S : Subgroup G) ⊓ (Q' : Subgroup G))) ≤
            Nat.card (↥((R : Subgroup G) ⊓ (Q : Subgroup G))) := by
  classical
  let P₀ : Sylow p G := Classical.choice (Sylow.nonempty)
  letI : Finite (Sylow p G) := P₀.finite_of_finiteIndex
  let Witness : Type _ :=
    { w : (Sylow p G × G × Sylow p G) //
        x ∉ (w.1 : Subgroup G) ∧ x ∈ (w.2.2 : Subgroup G) ∧
        w.2.1 * x * w.2.1⁻¹ ∈ (w.2.2 : Subgroup G) ∧
        w.2.1 * x * w.2.1⁻¹ ∈ (w.1 : Subgroup G) }
  have hn : Nonempty Witness := by
    rcases pair_witness_max_intersection x hyp Q₀ hm₀ with
      ⟨a, R, hx, hy, hq, _⟩
    exact ⟨⟨(Q₀, a, R), hm₀, hx, hy, hq⟩⟩
  letI : Nonempty Witness := hn
  have hm := Finite.exists_max (fun z : Witness =>
      Nat.card (↥(((z.1.2.2 : Sylow p G) : Subgroup G) ⊓
        ((z.1.1 : Sylow p G) : Subgroup G))))
  rcases hm with ⟨w, hw⟩
  rcases w with ⟨⟨Q,a,R⟩, ho, hx, hy, hq⟩
  refine ⟨Q,a,R,ho,hx,hy,hq,?_⟩
  intro Q' b S ho' hx' hy' hq'
  exact hw ⟨⟨Q',b,S⟩, ho',hx',hy',hq'⟩

end Foo

namespace Foo
open scoped Pointwise
/-- At a maximal bad pair the omitting Sylow cannot already be contained in
    the normalizer of the intersection.  If it is, conjugate in that
    normalizer a Sylow containing the other normalizer part onto it.  Pulling
    the omitting Sylow back gives a strictly larger bad pair. -/
lemma max_bad_Q_not_le {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x,hxH⟩ : H) ∈
        (sSup {L : Subgroup H | L.Normal ∧ IsPGroup p L} : Subgroup H))
    (Q R : Sylow p G) (a : G)
    (ho : x ∉ (Q : Subgroup G)) (hx : x ∈ (R : Subgroup G))
    (hy : a*x*a⁻¹ ∈ (R : Subgroup G)) (hq : a*x*a⁻¹ ∈ (Q : Subgroup G))
    (hNproper : Subgroup.normalizer
       (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) ≠ ⊤)
    (hmax : ∀ (Q' : Sylow p G) (b : G) (S : Sylow p G),
        x ∉ (Q' : Subgroup G) → x ∈ (S : Subgroup G) →
        b*x*b⁻¹ ∈ (S : Subgroup G) → b*x*b⁻¹ ∈ (Q' : Subgroup G) →
        Nat.card (↥((S : Subgroup G) ⊓ (Q' : Subgroup G))) ≤
          Nat.card (↥((R : Subgroup G) ⊓ (Q : Subgroup G)))) :
    ¬ ((Q : Subgroup G) ≤ Subgroup.normalizer
        (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)) := by
  classical
  let I : Subgroup G := (R : Subgroup G) ⊓ (Q : Subgroup G)
  let N : Subgroup G := Subgroup.normalizer (I : Set G)
  have hIR : I ≤ (R : Subgroup G) := inf_le_left
  have hIQ : I ≤ (Q : Subgroup G) := inf_le_right
  have hne : I ≠ (R : Subgroup G) := by
    intro e
    have : x ∈ I := e.symm ▸ hx
    exact ho (hIQ this)
  have hNp : N ≠ (⊤ : Subgroup G) := by simpa [N, I] using hNproper
  intro hQ
  have hQN : (Q : Subgroup G) ≤ N := by simpa [N,I] using hQ
  -- If `x` were in this proper normalizer, minimality already puts it in Q.
  have hxo : x ∉ N := by
    intro hxN
    have hc := hproper N hxN hNp
    have hm : (⟨x,hxN⟩ : N) ∈ (Q.subtype hQN : Sylow p N) :=
      (mem_sup_core_iff_mem_all_sylow p _).1 hc _
    exact ho hm
  -- Extend the R-part in `N` and move it onto `Q` there.
  let A : Subgroup N := (R : Subgroup G).subgroupOf N
  have hAp : IsPGroup p A :=
    IsPGroup.comap_of_injective R.isPGroup' N.subtype
      (Subgroup.subtype_injective N)
  obtain ⟨U, hAU⟩ := hAp.exists_le_sylow
  letI : Finite (Sylow p N) := (Q.subtype hQN).finite_of_finiteIndex
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N U (Q.subtype hQN)
  -- Put `d=c⁻¹`, in ambient notation; `Q' = d Q d⁻¹` is another
  -- omitting Sylow.  Its intersection with `R` contains all of `A`.
  let d : G := (c⁻¹ : N)
  let Q' : Sylow p G := d • Q
  have hdN : d ∈ N := (c⁻¹ : N).property
  have hdiN : d⁻¹ ∈ N := N.inv_mem hdN
  have hQ'N : (Q' : Subgroup G) ≤ N := by
    intro t ht
    -- membership in a conjugate set
    change t ∈ (MulAut.conj d • (Q : Set G)) at ht
    rw [Set.mem_smul_set] at ht
    rcases ht with ⟨q, hq0, rfl⟩
    exact N.mul_mem (N.mul_mem hdN (hQN hq0)) hdiN
  have hxQ' : x ∉ (Q' : Subgroup G) := fun hh => hxo (hQ'N hh)
  have hAQ' : ∀ z : G, z ∈ (R : Subgroup G) → z ∈ N →
      z ∈ (Q' : Subgroup G) := by
    intro z hz hzN
    let zN : N := ⟨z,hzN⟩
    have hzA : zN ∈ A := Subgroup.mem_subgroupOf.mpr hz
    have hzU : zN ∈ (U : Subgroup N) := hAU hzA
    have hzQ : c * zN * c⁻¹ ∈ (Q.subtype hQN : Subgroup N) := by
      -- transport membership by `hc`
      rw [← hc]
      change c * zN * c⁻¹ ∈ (MulAut.conj c • (U : Set N))
      rw [Set.mem_smul_set]
      exact ⟨zN, hzU, rfl⟩
    -- conjugating this assertion back says that `z` is in `d • Q`.
    change z ∈ (MulAut.conj d • (Q : Set G))
    rw [Set.mem_smul_set]
    refine ⟨((c : N) * zN * c⁻¹ : N) , ?_, ?_⟩
    · exact hzQ
    · change d * (((c : N) * zN * c⁻¹ : N) : G) * d⁻¹ = z
      change ((c⁻¹ : N) : G) *
          (((c : N) * zN * c⁻¹ : N) : G) *
          ((c⁻¹ : N) : G)⁻¹ = z
      have hh : (c : N)⁻¹ * ((c : N) * zN * (c : N)⁻¹) *
          ((c : N)⁻¹)⁻¹ = zN := by
        simp [mul_assoc]
      -- compare underlying elements in `G`
      exact congrArg (fun u : N => (u : G)) hh
  -- `I` is in the new intersection, and the normalizer condition in R
  -- gives a fresh point of it.
  have hI' : I ≤ ((R : Subgroup G) ⊓ (Q' : Subgroup G)) := by
    intro z hz
    exact ⟨hIR hz, hAQ' z (hIR hz) (Subgroup.le_normalizer hz)⟩
  obtain ⟨w, hwR, hwN, hwo⟩ :=
    exists_mem_sylow_normalizer_not_mem R I hIR hne
  have hwN' : w ∈ N := by simpa [N] using hwN
  have hstrict : I < ((R : Subgroup G) ⊓ (Q' : Subgroup G)) :=
    lt_of_le_not_ge hI' (by
      intro hb
      exact hwo (hb ⟨hwR, hAQ' w hwR hwN'⟩))
  -- the common conjugate can simply be moved backwards as well; `c` is in
  -- the normalizer, so it preserves `I`.
  have hyI : a*x*a⁻¹ ∈ I := ⟨hy, hq⟩
  have hyN : a*x*a⁻¹ ∈ N := Subgroup.le_normalizer hyI
  have hdconjI : d * (a*x*a⁻¹) * d⁻¹ ∈ I := by
    -- an element of `N(I)` conjugates `I` into itself
    exact (Subgroup.mem_normalizer_iff.mp hdN (a*x*a⁻¹)).1 hyI
  have hyR' : (d*a)*x*(d*a)⁻¹ ∈ (R : Subgroup G) := by
    have : d * (a*x*a⁻¹) * d⁻¹ ∈ I := hdconjI
    have heq : (d*a)*x*(d*a)⁻¹ = d * (a*x*a⁻¹) * d⁻¹ := by
      simp [mul_assoc]
    rw [heq]
    exact hIR this
  have hyQ' : (d*a)*x*(d*a)⁻¹ ∈ (Q' : Subgroup G) := by
    have : d * (a*x*a⁻¹) * d⁻¹ ∈ I := hdconjI
    have hi' := hI' this
    have heq : (d*a)*x*(d*a)⁻¹ = d * (a*x*a⁻¹) * d⁻¹ := by
      simp [mul_assoc]
    rw [heq]
    exact hi'.2
  have hbound := hmax Q' (d*a) R hxQ' hx hyR' hyQ'
  have hlt : Nat.card I <
      Nat.card (((R : Subgroup G) ⊓ (Q' : Subgroup G) : Subgroup G)) :=
    natCard_subgroup_lt_of_lt hstrict
  have hbound' : Nat.card
       (((R : Subgroup G) ⊓ (Q' : Subgroup G) : Subgroup G)) ≤
       Nat.card I := by simpa [I] using hbound
  exact (Nat.not_lt_of_ge hbound') hlt
end Foo

namespace Foo
/-- Symmetric easy obstruction.  If the containing Sylow is in the
normalizer, `x` as well as `y` is in the core there.  Extending the
normalizer part of the omitting Sylow gives a larger bad pair. -/
lemma max_bad_R_not_le {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {x : G}
    (hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
      (⟨x,hxH⟩ : H) ∈
        (sSup {L : Subgroup H | L.Normal ∧ IsPGroup p L} : Subgroup H))
    (Q R : Sylow p G) (a : G)
    (ho : x ∉ (Q : Subgroup G)) (hx : x ∈ (R : Subgroup G))
    (hy : a*x*a⁻¹ ∈ (R : Subgroup G)) (hq : a*x*a⁻¹ ∈ (Q : Subgroup G))
    (hNproper : Subgroup.normalizer
       (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) ≠ ⊤)
    (hall : ∀ U : Sylow p
        (Subgroup.normalizer
          (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)),
      (⟨a*x*a⁻¹, Subgroup.le_normalizer (show
        a*x*a⁻¹ ∈ ((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) from
          ⟨hy,hq⟩)⟩ :
        Subgroup.normalizer
          (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)) ∈ U)
    (hmax : ∀ (Q' : Sylow p G) (b : G) (S : Sylow p G),
        x ∉ (Q' : Subgroup G) → x ∈ (S : Subgroup G) →
        b*x*b⁻¹ ∈ (S : Subgroup G) → b*x*b⁻¹ ∈ (Q' : Subgroup G) →
        Nat.card (↥((S : Subgroup G) ⊓ (Q' : Subgroup G))) ≤
          Nat.card (↥((R : Subgroup G) ⊓ (Q : Subgroup G)))) :
    ¬ ((R : Subgroup G) ≤ Subgroup.normalizer
        (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)) := by
  classical
  let I : Subgroup G := (R : Subgroup G) ⊓ (Q : Subgroup G)
  let N : Subgroup G := Subgroup.normalizer (I : Set G)
  have hIR : I ≤ (R : Subgroup G) := inf_le_left
  have hIQ : I ≤ (Q : Subgroup G) := inf_le_right
  have hyI : a*x*a⁻¹ ∈ I := ⟨hy,hq⟩
  have hneQ : I ≠ (Q : Subgroup G) := by
    intro e
    have hqr : (Q : Subgroup G) ≤ (R : Subgroup G) := by
      rw [← e]; exact hIR
    have heq : (R : Subgroup G) = (Q : Subgroup G) :=
      Q.is_maximal' R.isPGroup' hqr
    exact ho (by rw [← heq]; exact hx)
  have hNp : N ≠ (⊤ : Subgroup G) := by simpa [N,I] using hNproper
  intro hR
  have hRN : (R : Subgroup G) ≤ N := by simpa [N,I] using hR
  have hxN : x ∈ N := hRN hx
  have hc := hproper N hxN hNp
  have hxall : ∀ T : Sylow p N, (⟨x,hxN⟩ : N) ∈ T :=
    (mem_sup_core_iff_mem_all_sylow p _).1 hc
  have hall' : ∀ U : Sylow p N,
      (⟨a*x*a⁻¹, Subgroup.le_normalizer hyI⟩ : N) ∈ U := by
    intro U
    dsimp [N,I] at U ⊢
    convert hall U
  obtain ⟨W, hyW, hxW, hlarge⟩ :=
    exists_sylow_with_larger_intersection_two Q I hIQ hneQ
      (a*x*a⁻¹) hyI (by simpa [N] using hall')
        x (by simpa [N] using hxN) (by simpa [N] using hxall)
  have hbnd := hmax Q a W ho hxW hyW hq
  have hlt0 : Nat.card I <
      Nat.card (((Q : Subgroup G) ⊓ (W : Subgroup G) : Subgroup G)) :=
    natCard_subgroup_lt_of_lt hlarge
  have he : ((Q : Subgroup G) ⊓ (W : Subgroup G) : Subgroup G) =
       ((W : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) := inf_comm _ _
  have hlt : Nat.card I <
      Nat.card (((W : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G)) := by
    simpa [he] using hlt0
  have hbnd' : Nat.card
      (((W : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G)) ≤ Nat.card I := by
    simpa [I] using hbnd
  exact (Nat.not_lt_of_ge hbnd') hlt
end Foo

namespace Foo
open scoped Pointwise
/-- Align the two normalizer parts.  This is the precise piece of the usual
Sylow-intersection argument which is valid without claiming that an extension
of a Sylow of a subgroup is contained in that subgroup. -/
lemma align_normalizer_parts {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (R Q : Sylow p G) (I : Subgroup G) :
    let N := Subgroup.normalizer (I : Set G)
    ∃ (c : N) (T : Sylow p G),
      (∀ z : G, z ∈ (R : Subgroup G) → z ∈ N →
          (c : G) * z * (c : G)⁻¹ ∈ (T : Subgroup G)) ∧
      (∀ z : G, z ∈ (Q : Subgroup G) → z ∈ N →
          z ∈ (T : Subgroup G)) := by
  classical
  intro N
  let A : Subgroup N := (R : Subgroup G).subgroupOf N
  let B : Subgroup N := (Q : Subgroup G).subgroupOf N
  have hpA : IsPGroup p A :=
    IsPGroup.comap_of_injective R.isPGroup' N.subtype
      (Subgroup.subtype_injective N)
  have hpB : IsPGroup p B :=
    IsPGroup.comap_of_injective Q.isPGroup' N.subtype
      (Subgroup.subtype_injective N)
  obtain ⟨U, hAU⟩ := hpA.exists_le_sylow
  obtain ⟨V, hBV⟩ := hpB.exists_le_sylow
  letI : Finite (Sylow p N) := U.finite_of_finiteIndex
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N U V
  have hmap (z : G) (hz : z ∈ (R : Subgroup G)) (hzN : z ∈ N) :
      (c : G) * z * (c : G)⁻¹ ∈
        Subgroup.map N.subtype (V : Subgroup N) := by
    let zN : N := ⟨z, hzN⟩
    have hzU : zN ∈ (U : Subgroup N) := hAU (Subgroup.mem_subgroupOf.mpr hz)
    have hzV : c * zN * c⁻¹ ∈ (V : Subgroup N) := by
      rw [← hc]
      change c * zN * c⁻¹ ∈ (MulAut.conj c • (U : Set N))
      rw [Set.mem_smul_set]
      exact ⟨zN, hzU, rfl⟩
    refine ⟨c * zN * c⁻¹, hzV, ?_⟩
    rfl
  have hpV : IsPGroup p (Subgroup.map N.subtype (V : Subgroup N)) :=
    IsPGroup.map V.isPGroup' N.subtype
  obtain ⟨T, hVT⟩ := hpV.exists_le_sylow
  refine ⟨c, T, ?_, ?_⟩
  · intro z hz hzN
    exact hVT (hmap z hz hzN)
  · intro z hz hzN
    have hzB : (⟨z,hzN⟩ : N) ∈ B := Subgroup.mem_subgroupOf.mpr hz
    have hzV : (⟨z,hzN⟩ : N) ∈ (V : Subgroup N) := hBV hzB
    exact hVT ⟨⟨z,hzN⟩, hzV, rfl⟩
end Foo

namespace Foo
open scoped Pointwise
lemma max_bad_cx_mem_of_aligned {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {x : G}
    (Q R T : Sylow p G) (I : Subgroup G) (a : G)
    (hdef : I = (R : Subgroup G) ⊓ (Q : Subgroup G))
    (ho : x ∉ (Q : Subgroup G)) (hx : x ∈ (R : Subgroup G))
    (hy : a*x*a⁻¹ ∈ (R : Subgroup G)) (hq : a*x*a⁻¹ ∈ (Q : Subgroup G))
    (hmax : ∀ (Q' : Sylow p G) (b : G) (S : Sylow p G),
        x ∉ (Q' : Subgroup G) → x ∈ (S : Subgroup G) →
        b*x*b⁻¹ ∈ (S : Subgroup G) → b*x*b⁻¹ ∈ (Q' : Subgroup G) →
        Nat.card (↥((S : Subgroup G) ⊓ (Q' : Subgroup G))) ≤
          Nat.card (↥((R : Subgroup G) ⊓ (Q : Subgroup G))))
    (c : Subgroup.normalizer (I : Set G))
    (hcR : ∀ z : G, z ∈ (R : Subgroup G) →
        z ∈ Subgroup.normalizer (I : Set G) →
          (c:G)*z*(c:G)⁻¹ ∈ (T : Subgroup G)) :
    (c:G)*x*(c:G)⁻¹ ∈ (T : Subgroup G) := by
  classical
  by_contra hnot
  let Q' : Sylow p G := (c:G)⁻¹ • T
  have hlift : ∀ z : G, (c:G)*z*(c:G)⁻¹ ∈ (T : Subgroup G) →
       z ∈ (Q' : Subgroup G) := by
    intro z hz
    change z ∈ (MulAut.conj ((c:G)⁻¹) • (T : Set G))
    rw [Set.mem_smul_set]
    refine ⟨(c:G)*z*(c:G)⁻¹, hz, ?_⟩
    simp [mul_assoc]
  have hQ'o : x ∉ (Q' : Subgroup G) := by
    intro he
    change x ∈ (MulAut.conj ((c:G)⁻¹) • (T : Set G)) at he
    rw [Set.mem_smul_set] at he
    rcases he with ⟨z,hz,hzeq⟩
    apply hnot
    -- conjugate the displayed equation by c
    have hh := congrArg (fun t : G => (c:G)*t*(c:G)⁻¹) hzeq
    have : (c:G)*x*(c:G)⁻¹ = z := by
      simpa [mul_assoc] using hh.symm
    rwa [this]
  have hIR : I ≤ (R : Subgroup G) := by rw [hdef]; exact inf_le_left
  have hIQ : I ≤ (Q : Subgroup G) := by rw [hdef]; exact inf_le_right
  have hne : I ≠ (R : Subgroup G) := by
    intro e
    exact ho (hIQ (e.symm ▸ hx))
  have hI' : I ≤ ((R : Subgroup G) ⊓ (Q' : Subgroup G)) := by
    intro z hz
    exact ⟨hIR hz,
      hlift z (hcR z (hIR hz) (Subgroup.le_normalizer hz))⟩
  obtain ⟨w, hwR, hwN, hout⟩ :=
    exists_mem_sylow_normalizer_not_mem R I hIR hne
  have hlarge : I < ((R : Subgroup G) ⊓ (Q' : Subgroup G)) :=
    lt_of_le_not_ge hI' (by
      intro hb
      exact hout (hb ⟨hwR, hlift w (hcR w hwR hwN)⟩))
  have hyI : a*x*a⁻¹ ∈ I := by rw [hdef]; exact ⟨hy,hq⟩
  have hyQ' : a*x*a⁻¹ ∈ (Q' : Subgroup G) :=
    hlift _ (hcR _ hy (Subgroup.le_normalizer hyI))
  have hb := hmax Q' a R hQ'o hx hy hyQ'
  have hlt : Nat.card I <
      Nat.card (((R : Subgroup G) ⊓ (Q' : Subgroup G) : Subgroup G)) :=
    natCard_subgroup_lt_of_lt hlarge
  have hb' : Nat.card (((R : Subgroup G) ⊓ (Q' : Subgroup G) : Subgroup G)) ≤
       Nat.card I := by simpa [hdef] using hb
  exact (Nat.not_lt_of_ge hb') hlt
end Foo

namespace Foo
lemma max_bad_x_not_mem_of_aligned {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {x : G}
    (Q R T : Sylow p G) (I : Subgroup G) (a : G)
    (hdef : I = (R : Subgroup G) ⊓ (Q : Subgroup G))
    (ho : x ∉ (Q : Subgroup G)) (hx : x ∈ (R : Subgroup G))
    (hy : a*x*a⁻¹ ∈ (R : Subgroup G)) (hq : a*x*a⁻¹ ∈ (Q : Subgroup G))
    (hmax : ∀ (Q' : Sylow p G) (b : G) (S : Sylow p G),
        x ∉ (Q' : Subgroup G) → x ∈ (S : Subgroup G) →
        b*x*b⁻¹ ∈ (S : Subgroup G) → b*x*b⁻¹ ∈ (Q' : Subgroup G) →
        Nat.card (↥((S : Subgroup G) ⊓ (Q' : Subgroup G))) ≤
          Nat.card (↥((R : Subgroup G) ⊓ (Q : Subgroup G))))
    (hcQ : ∀ z : G, z ∈ (Q : Subgroup G) →
        z ∈ Subgroup.normalizer (I : Set G) → z ∈ (T : Subgroup G)) :
    x ∉ (T : Subgroup G) := by
  classical
  intro hxT
  have hIR : I ≤ (R : Subgroup G) := by rw [hdef]; exact inf_le_left
  have hIQ : I ≤ (Q : Subgroup G) := by rw [hdef]; exact inf_le_right
  have hne : I ≠ (Q : Subgroup G) := by
    intro e
    have hQR : (Q : Subgroup G) ≤ (R : Subgroup G) := by rw [← e]; exact hIR
    have he : (R : Subgroup G) = (Q : Subgroup G) :=
      Q.is_maximal' R.isPGroup' hQR
    exact ho (by rw [← he]; exact hx)
  have hle : I ≤ ((Q : Subgroup G) ⊓ (T : Subgroup G)) := by
    intro z hz
    exact ⟨hIQ hz, hcQ z (hIQ hz) (Subgroup.le_normalizer hz)⟩
  obtain ⟨w, hwQ, hwN, hout⟩ :=
    exists_mem_sylow_normalizer_not_mem Q I hIQ hne
  have hlarge0 : I < ((Q : Subgroup G) ⊓ (T : Subgroup G)) :=
    lt_of_le_not_ge hle (by
      intro hb
      exact hout (hb ⟨hwQ, hcQ w hwQ hwN⟩))
  let y : G := a*x*a⁻¹
  have hyI : y ∈ I := by change a*x*a⁻¹ ∈ I; rw [hdef]; exact ⟨hy,hq⟩
  have hyT : a*x*a⁻¹ ∈ (T : Subgroup G) :=
    hcQ _ hq (Subgroup.le_normalizer hyI)
  have hb := hmax Q a T ho hxT hyT hq
  have heq : ((Q : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G) =
      ((T : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) := inf_comm _ _
  have hlt0 : Nat.card I <
       Nat.card (((Q : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G)) :=
    natCard_subgroup_lt_of_lt hlarge0
  have hlt : Nat.card I <
       Nat.card (((T : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G)) := by
    simpa [heq] using hlt0
  have hb' : Nat.card (((T : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G)) ≤
       Nat.card I := by simpa [hdef] using hb
  exact (Nat.not_lt_of_ge hb') hlt
end Foo

end
-- END INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/MaxBad.lean

-- BEGIN INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/Radical.lean
section

/-! The common conjugate in a maximum bad pair exhausts the local `p`-core
of its normalizer. This packages a useful extra part of the last local step:
if one has a further element of every Sylow of `N_G(I)`, augment *each* side
separately and then compare their two ambient extensions. The extensions are
not asserted to lie in the normalizer. -/
namespace Foo

lemma max_bad_normalizer_core_mem_inter
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {x : G}
    (Q R : Sylow p G) (a : G)
    (ho : x ∉ (Q : Subgroup G)) (hx : x ∈ (R : Subgroup G))
    (hy : a*x*a⁻¹ ∈ (R : Subgroup G)) (hq : a*x*a⁻¹ ∈ (Q : Subgroup G))
    (hmax : ∀ (Q' : Sylow p G) (b : G) (S : Sylow p G),
        x ∉ (Q' : Subgroup G) → x ∈ (S : Subgroup G) →
        b*x*b⁻¹ ∈ (S : Subgroup G) → b*x*b⁻¹ ∈ (Q' : Subgroup G) →
        Nat.card (↥((S : Subgroup G) ⊓ (Q' : Subgroup G))) ≤
          Nat.card (↥((R : Subgroup G) ⊓ (Q : Subgroup G))))
    (hall : ∀ U : Sylow p
        (Subgroup.normalizer
          (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)),
      (⟨a*x*a⁻¹, Subgroup.le_normalizer (show
        a*x*a⁻¹ ∈ ((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) from
          ⟨hy,hq⟩)⟩ :
        Subgroup.normalizer
          (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)) ∈ U)
    (z : G)
    (hzN : z ∈ Subgroup.normalizer
      (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G))
    (hallz : ∀ U : Sylow p
        (Subgroup.normalizer
          (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)),
      (⟨z,hzN⟩ :
        Subgroup.normalizer
          (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)) ∈ U) :
    z ∈ ((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) := by
  classical
  let I : Subgroup G := (R : Subgroup G) ⊓ (Q : Subgroup G)
  have hIR : I ≤ (R : Subgroup G) := inf_le_left
  have hIQ : I ≤ (Q : Subgroup G) := inf_le_right
  have hneR : I ≠ (R : Subgroup G) := by
    intro he
    have hxI : x ∈ I := by rw [he]; exact hx
    exact ho (hIQ hxI)
  have hneQ : I ≠ (Q : Subgroup G) := by
    intro he
    have hQR : (Q : Subgroup G) ≤ (R : Subgroup G) := by
      rw [← he]
      exact hIR
    have hEq : (R : Subgroup G) = (Q : Subgroup G) :=
      Q.is_maximal' R.isPGroup' hQR
    exact ho (by rw [← hEq]; exact hx)
  have hyI : a*x*a⁻¹ ∈ I := ⟨hy,hq⟩
  have hzN' : z ∈ Subgroup.normalizer (I : Set G) := by
    simpa [I] using hzN
  have hall' : ∀ U : Sylow p (Subgroup.normalizer (I : Set G)),
      (⟨a*x*a⁻¹, Subgroup.le_normalizer hyI⟩ :
        Subgroup.normalizer (I : Set G)) ∈ U := by
    simpa [I] using hall
  have hallz' : ∀ U : Sylow p (Subgroup.normalizer (I : Set G)),
      (⟨z,hzN'⟩ : Subgroup.normalizer (I : Set G)) ∈ U := by
    -- proof irrelevance identifies the subtype proof
    simpa [I] using hallz
  by_contra hzout0
  have hzout : z ∉ I := by simpa [I] using hzout0
  -- extend from each one of the two sides, keeping also this additional
  -- common normalizer-core element.
  obtain ⟨S, hyS, hzS, hlargeR⟩ :=
    exists_sylow_with_larger_intersection_two
      R I hIR hneR (a*x*a⁻¹) hyI hall' z hzN' hallz'
  obtain ⟨T, hyT, hzT, hlargeQ⟩ :=
    exists_sylow_with_larger_intersection_two
      Q I hIQ hneQ (a*x*a⁻¹) hyI hall' z hzN' hallz'

  -- The first extension necessarily *contains* x: if it omitted x the
  -- old containing side R itself and the same conjugate y would already be
  -- a larger bad pair.
  have hxS : x ∈ (S : Subgroup G) := by
    by_contra hxoS
    have hb := hmax S a R hxoS hx hy hyS
    have hb' : Nat.card (((R : Subgroup G) ⊓
        (S : Subgroup G) : Subgroup G)) ≤ Nat.card I := by
      simpa [I] using hb
    have hlt : Nat.card I < Nat.card (((R : Subgroup G) ⊓
        (S : Subgroup G) : Subgroup G)) :=
      natCard_subgroup_lt_of_lt hlargeR
    exact False.elim ((Nat.not_lt_of_ge hb') hlt)

  -- The second extension necessarily *omits* x, by the symmetric
  -- comparison with the old omitting side Q.
  have hxoT : x ∉ (T : Subgroup G) := by
    intro hxT
    have hb := hmax Q a T ho hxT hyT hq
    have he : ((Q : Subgroup G) ⊓
        (T : Subgroup G) : Subgroup G) =
      ((T : Subgroup G) ⊓
        (Q : Subgroup G) : Subgroup G) := inf_comm _ _
    have hlt0 : Nat.card I < Nat.card (((Q : Subgroup G) ⊓
        (T : Subgroup G) : Subgroup G)) :=
      natCard_subgroup_lt_of_lt hlargeQ
    have hlt : Nat.card I < Nat.card (((T : Subgroup G) ⊓
        (Q : Subgroup G) : Subgroup G)) := by
      simpa [he] using hlt0
    have hb' : Nat.card (((T : Subgroup G) ⊓
        (Q : Subgroup G) : Subgroup G)) ≤ Nat.card I := by
      simpa [I] using hb
    exact (Nat.not_lt_of_ge hb') hlt

  -- Both extensions contain all of `I`, and the additional element `z`.
  -- If it were outside `I` their mutual intersection is a strictly larger
  -- bad pair; it still has the very same common conjugate `a*x*a⁻¹`.
  have hIST : I ≤ ((S : Subgroup G) ⊓ (T : Subgroup G)) := by
    intro t ht
    exact ⟨hlargeR.le ht |>.2, hlargeQ.le ht |>.2⟩
  have hzST : z ∈ ((S : Subgroup G) ⊓ (T : Subgroup G) : Subgroup G) :=
    ⟨hzS,hzT⟩
  have hstr : I < ((S : Subgroup G) ⊓ (T : Subgroup G)) :=
    lt_of_le_not_ge hIST (by
      intro hh
      exact hzout (hh hzST))
  have hb := hmax T a S hxoT hxS hyS hyT
  have hlt : Nat.card I < Nat.card (((S : Subgroup G) ⊓
      (T : Subgroup G) : Subgroup G)) := natCard_subgroup_lt_of_lt hstr
  have hb' : Nat.card (((S : Subgroup G) ⊓
      (T : Subgroup G) : Subgroup G)) ≤ Nat.card I := by
    simpa [I] using hb
  exact False.elim ((Nat.not_lt_of_ge hb') hlt)

end Foo

namespace Foo
/-- Subgroup form of `max_bad_normalizer_core_mem_inter`.  In a maximum bad
pair the `p`-core of the proper normalizer, regarded back in the ambient
 group, is no larger than the displayed intersection. (Conversely the
intersection is a normal p-subgroup of that normalizer.) -/
lemma max_bad_normalizer_core_map_le
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {x : G}
    (Q R : Sylow p G) (a : G)
    (ho : x ∉ (Q : Subgroup G)) (hx : x ∈ (R : Subgroup G))
    (hy : a*x*a⁻¹ ∈ (R : Subgroup G)) (hq : a*x*a⁻¹ ∈ (Q : Subgroup G))
    (hmax : ∀ (Q' : Sylow p G) (b : G) (S : Sylow p G),
        x ∉ (Q' : Subgroup G) → x ∈ (S : Subgroup G) →
        b*x*b⁻¹ ∈ (S : Subgroup G) → b*x*b⁻¹ ∈ (Q' : Subgroup G) →
        Nat.card (↥((S : Subgroup G) ⊓ (Q' : Subgroup G))) ≤
          Nat.card (↥((R : Subgroup G) ⊓ (Q : Subgroup G))))
    (hall : ∀ U : Sylow p
        (Subgroup.normalizer
          (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)),
      (⟨a*x*a⁻¹, Subgroup.le_normalizer (show
        a*x*a⁻¹ ∈ ((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) from
          ⟨hy,hq⟩)⟩ :
        Subgroup.normalizer
          (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)) ∈ U) :
    let I : Subgroup G := (R : Subgroup G) ⊓ (Q : Subgroup G)
    let N : Subgroup G := Subgroup.normalizer (I : Set G)
    Subgroup.map N.subtype
      (sSup {L : Subgroup N | L.Normal ∧ IsPGroup p L} : Subgroup N) ≤ I := by
  classical
  dsimp
  intro z hz
  rcases hz with ⟨w, hw, rfl⟩
  -- the representative w lies in every Sylow of the normalizer
  have hwN : (w : G) ∈ Subgroup.normalizer
      (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G) :=
    w.property
  have hwa : ∀ U : Sylow p
      (Subgroup.normalizer
        (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)),
      (w : Subgroup.normalizer
        (((R : Subgroup G) ⊓ (Q : Subgroup G) : Subgroup G) : Set G)) ∈ U :=
    (mem_sup_core_iff_mem_all_sylow p _).1 hw
  apply max_bad_normalizer_core_mem_inter Q R a ho hx hy hq hmax hall
    (w : G) hwN
  intro U
  exact hwa U
end Foo
namespace Foo
/-- The reverse containment is elementary (the intersection is itself normal
in its normalizer). We state it separately without maximality assumptions. -/
lemma subgroup_le_normalizer_core_map
    {G : Type*} [Group G] {p : ℕ}
    (I : Subgroup G) (hIp : IsPGroup p I) :
    let N : Subgroup G := Subgroup.normalizer (I : Set G)
    I ≤ Subgroup.map N.subtype
      (sSup {L : Subgroup N | L.Normal ∧ IsPGroup p L} : Subgroup N) := by
  classical
  dsimp
  intro z hz
  let N : Subgroup G := Subgroup.normalizer (I : Set G)
  let J : Subgroup N := I.subgroupOf N
  have hnle : N ≤ Subgroup.normalizer (I : Set G) := by rfl
  have Jn : J.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnle
  have Jp : IsPGroup p J :=
    IsPGroup.comap_of_injective hIp N.subtype
      (Subgroup.subtype_injective N)
  have Jle : J ≤
      (sSup {L : Subgroup N | L.Normal ∧ IsPGroup p L} : Subgroup N) := by
    exact le_sSup ⟨Jn, Jp⟩
  have hzN : z ∈ N := Subgroup.le_normalizer hz
  have hzJ : (⟨z,hzN⟩ : N) ∈ J :=
    Subgroup.mem_subgroupOf.mpr hz
  exact ⟨(⟨z,hzN⟩ : N), Jle hzJ, rfl⟩
end Foo
namespace Foo
/-- If conjugation in both directions takes every class element which lies in
`I` back into `I`, it normalizes the subgroup generated by those elements.
Keeping this closure in the ambient group avoids coercions of conjugating
homomorphisms between subgroup types. -/
lemma mem_normalizer_closure_conj_of_preserves
 {G : Type*} [Group G] (x : G) (I : Subgroup G) (c : G)
 (hfor : ∀ t : G, t ∈ I →
   (∃ g : G, t = g*x*g⁻¹) → c*t*c⁻¹ ∈ I)
 (hback : ∀ t : G, t ∈ I →
   (∃ g : G, t = g*x*g⁻¹) → c⁻¹*t*(c⁻¹)⁻¹ ∈ I) :
 c ∈ Subgroup.normalizer
   (Subgroup.closure ({t : G | t ∈ I ∧ ∃ g : G, t = g*x*g⁻¹} : Set G) : Set G) := by
 classical
 let X : Set G := {t : G | t ∈ I ∧ ∃ g : G, t = g*x*g⁻¹}
 let J : Subgroup G := Subgroup.closure X
 have step (d : G)
    (hd : ∀ t : G, t ∈ I →
      (∃ g : G, t = g*x*g⁻¹) → d*t*d⁻¹ ∈ I)
    (z : G) (hz : z ∈ J) : d*z*d⁻¹ ∈ J := by
   change z ∈ Subgroup.closure X at hz
   induction hz using Subgroup.closure_induction with
   | mem z hz =>
       apply Subgroup.subset_closure
       change d*z*d⁻¹ ∈ X
       rcases hz with ⟨hzI,g,hg⟩
       refine ⟨hd z hzI ⟨g,hg⟩, ?_⟩
       refine ⟨d*g, ?_⟩
       rw [hg]
       simp [mul_assoc]
   | one => simp [J]
   | mul z w hz hw iz iw =>
       have he : (d*z*d⁻¹) * (d*w*d⁻¹) ∈ J := J.mul_mem iz iw
       simpa [mul_assoc] using he
   | inv z hz ih =>
       have he : (d*z*d⁻¹)⁻¹ ∈ J := J.inv_mem ih
       simpa [mul_assoc] using he
 have hf (z : G) (hz : z ∈ J) : c*z*c⁻¹ ∈ J := step c hfor z hz
 have hb (z : G) (hz : z ∈ J) : c⁻¹*z*(c⁻¹)⁻¹ ∈ J := step (c⁻¹) hback z hz
 change c ∈ Subgroup.normalizer (J : Set G)
 apply Subgroup.mem_normalizer_iff.mpr
 intro t
 constructor
 · exact hf t
 · intro hcon
   have hh := hb (c*t*c⁻¹) hcon
   simpa [mul_assoc] using hh
end Foo

end
-- END INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/Radical.lean

-- BEGIN INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/Iterate.lean
section

/-! A variant of the extension construction recording the *whole* normalizer
part of a chosen ambient Sylow.  Unlike the strict-enlargement corollary this
version has no maximality hypothesis.  It is useful when changing to a
smaller characteristic subgroup while retaining the old intersection. -/
namespace Foo
lemma exists_sylow_containing_normalizer_part_two
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R : Sylow p G) (K : Subgroup G)
    (y : G) (hyK : y ∈ K)
    (hall : ∀ U : Sylow p (Subgroup.normalizer (K : Set G)),
      (⟨y, Subgroup.le_normalizer hyK⟩ :
        Subgroup.normalizer (K : Set G)) ∈ U)
    (z : G) (hzN : z ∈ Subgroup.normalizer (K : Set G))
    (hallz : ∀ U : Sylow p (Subgroup.normalizer (K : Set G)),
      (⟨z, hzN⟩ : Subgroup.normalizer (K : Set G)) ∈ U) :
    ∃ T : Sylow p G,
      y ∈ (T : Subgroup G) ∧ z ∈ (T : Subgroup G) ∧
      ∀ t : G, t ∈ (R : Subgroup G) →
        t ∈ Subgroup.normalizer (K : Set G) → t ∈ (T : Subgroup G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (K : Set G)
  let A : Subgroup N := (R : Subgroup G).subgroupOf N
  have hAp : IsPGroup p A :=
    IsPGroup.comap_of_injective R.isPGroup' N.subtype
      (Subgroup.subtype_injective N)
  obtain ⟨U, hAU⟩ := hAp.exists_le_sylow
  have hUp : IsPGroup p (Subgroup.map N.subtype (U : Subgroup N)) :=
    IsPGroup.map U.isPGroup' N.subtype
  obtain ⟨T, hUT⟩ := hUp.exists_le_sylow
  refine ⟨T, ?_, ?_, ?_⟩
  · apply hUT
    have hyN : y ∈ N := Subgroup.le_normalizer hyK
    refine ⟨(⟨y, hyN⟩ : N), ?_, rfl⟩
    exact hall U
  · apply hUT
    have hzN' : z ∈ N := hzN
    refine ⟨(⟨z, hzN'⟩ : N), ?_, rfl⟩
    exact hallz U
  · intro t htR htN
    apply hUT
    have htN' : t ∈ N := htN
    refine ⟨(⟨t, htN'⟩ : N), ?_, rfl⟩
    apply hAU
    exact (Subgroup.mem_subgroupOf.mpr htR)
end Foo

end
-- END INLINED FILE: Mathlib/Support/baer_suzuki_4490522689/Iterate.lean

-- BEGIN INLINED MAIN PRELUDE

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs
open scoped Pointwise
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem baer_suzuki {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (x : G) :
    x ∈ pCore p G ↔
      ∀ g : G, IsPGroup p
        (Subgroup.closure ({x, g * x * g⁻¹} : Set G)) :=
/-ResultProofBegin-/by
  classical
  change (x ∈ (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} : Subgroup G)) ↔ _
  constructor
  · intro hx
    exact Foo.forward p x hx
  · intro hyp
    induction hcard : Nat.card G using Nat.strong_induction_on generalizing G with
    | h n ih =>
      let C : Subgroup G :=
        (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} : Subgroup G)
      have Cn : C.Normal := Foo.sup_core_normal p
      letI : C.Normal := Cn
      have Cp : IsPGroup p C := Foo.sup_core_isPGroup p
      by_cases hc0 : C = ⊥
      · by_cases hxcent : x ∈ Subgroup.center G
        · simpa [C, hc0] using
            Foo.pair_hyp_mem_sup_core_of_mem_center hyp hxcent
        · by_cases hns : ∃ P : Sylow p G, (P : Subgroup G).Normal
          · obtain ⟨P,hP⟩ := hns
            letI : (P : Subgroup G).Normal := hP
            simpa [C, hc0] using
              (Foo.pair_hyp_mem_sup_core_of_normal_sylow x hyp P)
          · have hproper : ∀ (H : Subgroup G) (hxH : x ∈ H), H ≠ ⊤ →
                (⟨x,hxH⟩ : H) ∈
                  (sSup {Q : Subgroup H | Q.Normal ∧ IsPGroup p Q} : Subgroup H) := by
              intro H hxH hHt
              have hsub := Foo.restrict_pair_hyp_to_subgroup hxH hyp
              have hnot : ¬ Function.Surjective (fun z : H => (z : G)) := by
                intro hs
                apply hHt
                apply (Subgroup.eq_top_iff' H).2
                intro y
                rcases hs y with ⟨z,hz⟩
                rw [← hz]
                exact z.property
              have hlt : Nat.card H < n := by
                rw [← hcard]
                letI := Fintype.ofFinite H
                letI := Fintype.ofFinite G
                rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
                exact Fintype.card_lt_of_injective_not_surjective _
                  Subtype.coe_injective hnot
              exact ih _ hlt (⟨x,hxH⟩ : H) hsub rfl
            let H0 : Subgroup G := Subgroup.normalClosure ({x} : Set G)
            have hx0 : x ∈ H0 := Subgroup.subset_normalClosure (by simp)
            have hn0 : H0.Normal := Subgroup.normalClosure_normal
            by_cases hgen : H0 = ⊤
            · have hjoin : ∀ Q : Sylow p G,
                    let T : Subgroup G :=
                      Subgroup.closure ({x}:Set G) ⊔ (Q : Subgroup G)
                    T = ⊤ ∨ x ∈ Q := by
                  intro Q
                  let T : Subgroup G :=
                    Subgroup.closure ({x}:Set G) ⊔ (Q : Subgroup G)
                  by_cases ht : T = ⊤
                  · exact Or.inl ht
                  · right
                    have hxcl : x ∈ Subgroup.closure ({x}:Set G) :=
                      Subgroup.subset_closure (by simp)
                    have hxT : x ∈ T :=
                      (show Subgroup.closure ({x}:Set G) ≤ T from le_sup_left) hxcl
                    have hQT : (Q : Subgroup G) ≤ T := le_sup_right
                    have hxcoreT := hproper T hxT ht
                    have hxR : (⟨x,hxT⟩ : T) ∈
                        (Q.subtype hQT : Sylow p T) := by
                      exact (Foo.mem_sup_core_iff_mem_all_sylow p
                        (⟨x,hxT⟩ : T)).1 hxcoreT (Q.subtype hQT)
                    change x ∈ Q at *
                    exact hxR
              refine (Foo.mem_sup_core_iff_mem_all_sylow p x).2 ?_
              intro Q
              rcases hjoin Q with htop | hxQ
              · by_cases hxnormQ :
                    x ∈ Subgroup.normalizer (Q : Subgroup G)
                · exact Foo.pair_hyp_mem_sylow_of_mem_normalizer x hyp Q hxnormQ
                · have hxnotQ : x ∉ (Q : Subgroup G) := by
                    intro hx'
                    exact hxnormQ (Subgroup.le_normalizer hx')
                  -- The genuinely difficult leftover is the usual minimal
                  -- counterexample: O_p(G)=1, x is not central, G has no
                  -- normal Sylow subgroup, its normal closure is all of G,
                  -- and every proper overgroup of x has x in its p-core.
                  -- Here Q is a Sylow with <x,Q>=G and x∉N(Q).
                  -- Every normalizer of a Sylow is proper here.  Minimality
                  -- therefore gives the strong local obstruction that no
                  -- conjugate of `x` occurs in `N_G(Q) \ Q`.
                  have hNQ : Subgroup.normalizer (Q : Set G) ≠
                        (⊤ : Subgroup G) := by
                    intro hh
                    have hn : (Q : Subgroup G).Normal :=
                      Subgroup.normalizer_eq_top_iff.mp hh
                    exact hns ⟨Q, hn⟩
                  have havoid : ∀ (a : G),
                        a * x * a⁻¹ ∈ Subgroup.normalizer (Q : Set G) →
                          a * x * a⁻¹ ∈ (Q : Subgroup G) := by
                    intro a ha
                    exact Foo.conj_mem_sylow_of_mem_normalizer_of_hproper
                      hproper Q hNQ a ha
                  have hx1 : x ≠ (1 : G) := by
                    intro hxone
                    apply hxcent
                    simpa [hxone] using (Subgroup.one_mem (Subgroup.center G))
                  -- In addition to the local normalizer facts it is helpful to
                  -- start with a *maximal bad pair*.  Both Sylows are allowed
                  -- to vary.  This is a finite choice (see `MaxBad`); without
                  -- it an extension out of the normalizer carries no
                  -- comparison invariant.
                  exfalso
                  obtain ⟨Q₁, a, R, homit, hxR, hyR, hyQ, hmax⟩ :=
                    Foo.bad_pair_max_intersection x hyp Q hxnotQ
                  let I : Subgroup G :=
                    (R : Subgroup G) ⊓ (Q₁ : Subgroup G)
                  have hyI : a * x * a⁻¹ ∈ I := ⟨hyR, hyQ⟩
                  have hIp : IsPGroup p I :=
                    IsPGroup.to_le R.isPGroup'
                      (show I ≤ (R : Subgroup G) from inf_le_left)
                  have hIR : I ≤ (R : Subgroup G) := inf_le_left
                  have hIQ : I ≤ (Q₁ : Subgroup G) := inf_le_right
                  have hneR : I ≠ (R : Subgroup G) := by
                    intro he
                    have hm : x ∈ I := by
                      rw [he]
                      exact hxR
                    exact homit (hIQ hm)
                  have hneQ : I ≠ (Q₁ : Subgroup G) := by
                    intro he
                    have hQR : (Q₁ : Subgroup G) ≤ (R : Subgroup G) := by
                      rw [← he]
                      exact hIR
                    have hEq : (R : Subgroup G) = (Q₁ : Subgroup G) :=
                      Q₁.is_maximal' R.isPGroup' hQR
                    apply homit
                    rw [← hEq]
                    exact hxR
                  have hNI : Subgroup.normalizer (I : Set G) ≠
                         (⊤ : Subgroup G) :=
                    Foo.normalizer_ne_top_of_conj_mem_of_core_eq_bot
                      (by simpa [C] using hc0) hx1 I hIp a hyI
                  have hall :
                      ∀ U : Sylow p (Subgroup.normalizer (I : Set G)),
                        (⟨a * x * a⁻¹, Subgroup.le_normalizer hyI⟩ :
                          Subgroup.normalizer (I : Set G)) ∈ U := by
                    exact Foo.conj_mem_all_sylow_of_normalizer_of_core_eq_bot
                      (by simpa [C] using hc0) hx1 hproper I hIp a hyI
                  -- Besides the two ordinary one-sided extensions, maximality
                  -- deals rigorously with the cases where either side is
                  -- already contained in the normalizer.  The latter
                  -- assertion is slightly subtle for the omitting side: one
                  -- conjugates a Sylow *inside* `N_G(I)` onto it and pulls it
                  -- back; allowing the omitting Sylow to vary is essential.
                  obtain ⟨U, hyU, hIU⟩ :=
                    Foo.exists_sylow_with_larger_intersection
                      R I hIR hneR (a * x * a⁻¹) hyI hall
                  obtain ⟨V, hyV, hIV⟩ :=
                    Foo.exists_sylow_with_larger_intersection
                      Q₁ I hIQ hneQ (a * x * a⁻¹) hyI hall
                  have hRout : ¬ (R : Subgroup G) ≤
                        Subgroup.normalizer (I : Set G) := by
                    apply Foo.max_bad_R_not_le (x:=x) hproper Q₁ R a
                      homit hxR hyR hyQ (by simpa [I] using hNI)
                      (by simpa [I] using hall)
                    exact hmax
                  have hQout : ¬ (Q₁ : Subgroup G) ≤
                        Subgroup.normalizer (I : Set G) := by
                    apply Foo.max_bad_Q_not_le (x:=x) hproper Q₁ R a
                      homit hxR hyR hyQ (by simpa [I] using hNI)
                    exact hmax
                  -- In fact the element itself is outside this normalizer. If
                  -- it were not, its local core supplies `x` to the extension
                  -- on the omitting side, contradicting the same maximum.
                  have hxNIout : x ∉ Subgroup.normalizer (I : Set G) := by
                    intro hxNI
                    have hxall : ∀ W : Sylow p
                        (Subgroup.normalizer (I : Set G)),
                        (⟨x, hxNI⟩ :
                          Subgroup.normalizer (I : Set G)) ∈ W := by
                      have hm := hproper
                        (Subgroup.normalizer (I : Set G)) hxNI hNI
                      exact (Foo.mem_sup_core_iff_mem_all_sylow p _).1 hm
                    obtain ⟨W, hyW', hxW', hW'⟩ :=
                      Foo.exists_sylow_with_larger_intersection_two
                        Q₁ I hIQ hneQ (a*x*a⁻¹) hyI hall
                          x hxNI hxall
                    have hb := hmax Q₁ a W homit hxW' hyW' hyQ
                    have hh : Nat.card I <
                        Nat.card (((Q₁ : Subgroup G) ⊓
                          (W : Subgroup G) : Subgroup G)) :=
                      Foo.natCard_subgroup_lt_of_lt hW'
                    have he : ((Q₁ : Subgroup G) ⊓
                          (W : Subgroup G) : Subgroup G) =
                         ((W : Subgroup G) ⊓
                          (Q₁ : Subgroup G) : Subgroup G) := inf_comm _ _
                    have hh' : Nat.card I <
                        Nat.card (((W : Subgroup G) ⊓
                          (Q₁ : Subgroup G) : Subgroup G)) := by
                      simpa [he] using hh
                    have hb' : Nat.card (((W : Subgroup G) ⊓
                          (Q₁ : Subgroup G) : Subgroup G)) ≤ Nat.card I := by
                      simpa [I] using hb
                    exact (Nat.not_lt_of_ge hb') hh'
                  -- The two normalizer parts themselves can always be
                  -- aligned. This precise statement deliberately says that
                  -- their **extension** is a Sylow of `G`, not that it is
                  -- contained in the normalizer.
                  obtain ⟨cN, T, hcR, hcQ⟩ :=
                    Foo.align_normalizer_parts R Q₁ I
                  -- Maximality says more about this extension. It must
                  -- contain `c*x*c⁻¹`, but it cannot contain `x`.  Both tiny
                  -- observations are useful; assuming implicitly the second
                  -- inclusion is the pitfall in a naive argument here.
                  have hcxT : (cN : G)*x*(cN : G)⁻¹ ∈
                      (T : Subgroup G) :=
                    Foo.max_bad_cx_mem_of_aligned Q₁ R T I a rfl
                      homit hxR hyR hyQ hmax cN hcR
                  have hxT_out : x ∉ (T : Subgroup G) :=
                    Foo.max_bad_x_not_mem_of_aligned Q₁ R T I a rfl
                      homit hxR hyR hyQ hmax hcQ
                  have hcxNIout : (cN : G)*x*(cN : G)⁻¹ ∉
                      Subgroup.normalizer (I : Set G) := by
                    intro hm
                    apply hxNIout
                    have cin : (cN : G) ∈
                        Subgroup.normalizer (I : Set G) := cN.property
                    have ci : (cN : G)⁻¹ ∈
                        Subgroup.normalizer (I : Set G) :=
                      (Subgroup.normalizer (I : Set G)).inv_mem cin
                    have hh : (cN : G)⁻¹ *
                        ((cN : G)*x*(cN : G)⁻¹) * (cN : G) ∈
                        Subgroup.normalizer (I : Set G) :=
                      (Subgroup.normalizer (I : Set G)).mul_mem
                        ((Subgroup.normalizer (I : Set G)).mul_mem ci hm) cin
                    simpa [mul_assoc] using hh
                  -- The only case still to synchronize is therefore the
                  -- genuine two-sided one: both `R` and `Q₁` leave `N(I)`.
                  -- The earlier reductions by minimality continue to apply,
                  -- and if the containing side ever moved into `N(I)` the
                  -- following stronger extension would close it immediately.
                  have hnext :
                      (R : Subgroup G) ≤ Subgroup.normalizer (I : Set G) →
                        ∃ W : Sylow p G,
                          a * x * a⁻¹ ∈ (W : Subgroup G) ∧
                          x ∈ (W : Subgroup G) ∧
                            I < ((Q₁ : Subgroup G) ⊓ (W : Subgroup G)) := by
                    intro hRN
                    have hxNI : x ∈ Subgroup.normalizer (I : Set G) :=
                      hRN hxR
                    have hxall : ∀ W : Sylow p
                        (Subgroup.normalizer (I : Set G)),
                        (⟨x, hxNI⟩ :
                          Subgroup.normalizer (I : Set G)) ∈ W := by
                      have hm := hproper
                        (Subgroup.normalizer (I : Set G)) hxNI hNI
                      exact (Foo.mem_sup_core_iff_mem_all_sylow p _).1 hm
                    exact Foo.exists_sylow_with_larger_intersection_two
                      Q₁ I hIQ hneQ (a * x * a⁻¹) hyI hall
                        x hxNI hxall
                  -- Notice that the aligned `T` has opposite behaviours
                  -- for `x` and its `N(I)`-translate: `hcxT`, `hxT_out`, and
                  -- `hcxNIout`.  What remains is precisely the iteration/fusion
                  -- of such translates outside the proper normalizer; no
                  -- extension-to-Sylow step is silently identifying `T` with a
                  -- subgroup of it.
                  -- A useful last fully local deduction is that `I`
                  -- exhausts the *whole p-core* of its proper normalizer.  If
                  -- some additional element sat in every Sylow there, apply
                  -- the two-elt extension to R and Q separately.  The former
                  -- must be containing while the latter must be omitting by
                  -- maximality; their common extra element gives an even
                  -- larger bad pair.  This does not conflate either ambient
                  -- extension with a subgroup of the normalizer.
                  let D : Subgroup G := Subgroup.map
                    (Subgroup.normalizer (I : Set G)).subtype
                    (sSup {L : Subgroup (Subgroup.normalizer (I : Set G)) |
                      L.Normal ∧ IsPGroup p L} :
                      Subgroup (Subgroup.normalizer (I : Set G)))
                  have hDle : D ≤ I := by
                    dsimp [D]
                    have hm := Foo.max_bad_normalizer_core_map_le
                      Q₁ R a homit hxR hyR hyQ hmax
                      (by simpa [I] using hall)
                    simpa [I] using hm
                  have hIleD : I ≤ D := by
                    dsimp [D]
                    exact Foo.subgroup_le_normalizer_core_map I hIp
                  have hDeqI : D = I := le_antisymm hDle hIleD
                  -- All conjugates which happen to be in this normalizer
                  -- consequently lie in I itself.  This is stronger than the
                  -- earlier information for the single chosen conjugate y.
                  -- Minimality transports to a conjugate in a proper
                  -- overgroup before using the preceding core equality.
                  have hclassN : ∀ (g : G),
                      g*x*g⁻¹ ∈ Subgroup.normalizer (I : Set G) →
                         g*x*g⁻¹ ∈ I := by
                    intro g hg
                    have hgc : (⟨g*x*g⁻¹, hg⟩ :
                        Subgroup.normalizer (I : Set G)) ∈
                        (sSup {L : Subgroup (Subgroup.normalizer (I : Set G)) |
                          L.Normal ∧ IsPGroup p L} :
                          Subgroup (Subgroup.normalizer (I : Set G))) :=
                      Foo.conj_mem_sup_core_of_hproper hproper g
                        (Subgroup.normalizer (I : Set G)) hg hNI
                    have hgm : g*x*g⁻¹ ∈ D := by
                      refine ⟨(⟨g*x*g⁻¹, hg⟩ :
                        Subgroup.normalizer (I : Set G)), hgc, rfl⟩
                    exact hDle hgm
                  -- The actual one-sided extensions `U,V` above are forced
                  -- onto opposite sides of x.  They furnish a new maximum
                  -- bad pair with the same intersection; later arguments may
                  -- replace the old choice without any accidental claim U≤N.
                  have hxU : x ∈ (U : Subgroup G) := by
                    by_contra hxUo
                    have hb := hmax U a R hxUo hxR hyR hyU
                    have hb' : Nat.card (((R : Subgroup G) ⊓
                        (U : Subgroup G) : Subgroup G)) ≤ Nat.card I := by
                      simpa [I] using hb
                    have hh : Nat.card I < Nat.card
                        (((R : Subgroup G) ⊓
                         (U : Subgroup G) : Subgroup G)) :=
                      Foo.natCard_subgroup_lt_of_lt hIU
                    exact False.elim ((Nat.not_lt_of_ge hb') hh)
                  have hxVout : x ∉ (V : Subgroup G) := by
                    intro hxV
                    have hb := hmax Q₁ a V homit hxV hyV hyQ
                    have hh0 : Nat.card I < Nat.card
                        (((Q₁ : Subgroup G) ⊓
                         (V : Subgroup G) : Subgroup G)) :=
                      Foo.natCard_subgroup_lt_of_lt hIV
                    have he : ((Q₁ : Subgroup G) ⊓
                        (V : Subgroup G) : Subgroup G) =
                         ((V : Subgroup G) ⊓
                        (Q₁ : Subgroup G) : Subgroup G) := inf_comm _ _
                    have hh : Nat.card I < Nat.card
                        (((V : Subgroup G) ⊓
                         (Q₁ : Subgroup G) : Subgroup G)) := by
                      simpa [he] using hh0
                    have hb' : Nat.card (((V : Subgroup G) ⊓
                         (Q₁ : Subgroup G) : Subgroup G)) ≤ Nat.card I := by
                      simpa [I] using hb
                    exact (Nat.not_lt_of_ge hb') hh
                  have hIeUV :
                      I = ((U : Subgroup G) ⊓
                            (V : Subgroup G) : Subgroup G) := by
                    -- both strict enlargements still contain I and y
                    have hls : I ≤ ((U : Subgroup G) ⊓
                            (V : Subgroup G) : Subgroup G) := by
                      intro t ht
                      have hu : t ∈ (U : Subgroup G) := (hIU.le ht).2
                      have hv : t ∈ (V : Subgroup G) := (hIV.le ht).2
                      exact ⟨hu,hv⟩
                    have hb := hmax V a U hxVout hxU hyU hyV
                    have hlecard : Nat.card
                        (((U : Subgroup G) ⊓
                         (V : Subgroup G) : Subgroup G)) ≤ Nat.card I := by
                      simpa [I] using hb
                    -- finite subgroup inclusion and equal card -> equality
                    apply le_antisymm hls
                    by_contra hnot
                    have hstrict : I < ((U : Subgroup G) ⊓
                            (V : Subgroup G) : Subgroup G) :=
                      lt_of_le_not_ge hls hnot
                    have hcard : Nat.card I < Nat.card
                        (((U : Subgroup G) ⊓
                         (V : Subgroup G) : Subgroup G)) :=
                      Foo.natCard_subgroup_lt_of_lt hstrict
                    exact (Nat.not_lt_of_ge hlecard) hcard
                  -- Shrink once more to the subgroup generated only
                  -- by class elements in I. Its ambient normalizer is
                  -- strictly larger than N(I): a normalizer-condition point
                  -- of R∩N(I) already normalizes this smaller closure. This
                  -- sharpens the remaining radical two-sided case.
                  let J : Subgroup G := Subgroup.closure
                    ({t : G | t ∈ I ∧ ∃ g : G, t = g*x*g⁻¹} : Set G)
                  have hJI : J ≤ I := by
                    apply (Subgroup.closure_le _).2
                    intro t ht
                    exact ht.1
                  have hyJ : a*x*a⁻¹ ∈ J := by
                    apply Subgroup.subset_closure
                    exact ⟨hyI, ⟨a, rfl⟩⟩
                  have hNJ : Subgroup.normalizer (I : Set G) ≤
                      Subgroup.normalizer (J : Set G) := by
                    intro d hd
                    have hd' := Subgroup.mem_normalizer_iff.mp hd
                    exact Foo.mem_normalizer_closure_conj_of_preserves x I d
                      (by
                        intro t htI ht
                        exact (hd' t).1 htI)
                      (by
                        intro t htI ht
                        -- same normalizer with inverse direction
                        exact (Subgroup.mem_normalizer_iff.mp
                          ((Subgroup.normalizer (I : Set G)).inv_mem hd) t).1 htI)
                  -- the R-part of the normalizer is a proper subgroup of R;
                  -- its p-normalizer in R supplies a genuinely new element
                  let A : Subgroup G :=
                    (R : Subgroup G) ⊓ Subgroup.normalizer (I : Set G)
                  have hIA : I ≤ A := by
                    intro t ht
                    exact ⟨hIR ht, Subgroup.le_normalizer ht⟩
                  have hAR : A ≤ (R : Subgroup G) := inf_le_left
                  have hAne : A ≠ (R : Subgroup G) := by
                    intro he
                    apply hRout
                    intro t ht
                    have : t ∈ A := by rw [he]; exact ht
                    exact this.2
                  obtain ⟨d, hdR, hdA, hdout⟩ :=
                    Foo.exists_mem_sylow_normalizer_not_mem R A hAR hAne
                  have hdNIout : d ∉ Subgroup.normalizer (I : Set G) := by
                    intro hd
                    exact hdout ⟨hdR, hd⟩
                  have hdAJ : d ∈ Subgroup.normalizer (J : Set G) := by
                    have hdAn := Subgroup.mem_normalizer_iff.mp hdA
                    -- a conjugate lying back in A also lies in N(I);
                    -- hclassN then forces it to return to I
                    apply Foo.mem_normalizer_closure_conj_of_preserves x I d
                    · intro t htI ht
                      have htA : t ∈ A := hIA htI
                      have htAd : d*t*d⁻¹ ∈ A := (hdAn t).1 htA
                      rcases ht with ⟨g,hg⟩
                      have htc : d*t*d⁻¹ = (d*g)*x*(d*g)⁻¹ := by
                        rw [hg]
                        simp [mul_assoc]
                      rw [htc] at htAd ⊢
                      exact hclassN (d*g) htAd.2
                    · intro t htI ht
                      have hdAi : d⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
                        (Subgroup.normalizer (A : Set G)).inv_mem hdA
                      have htA : t ∈ A := hIA htI
                      have htAd : d⁻¹*t*(d⁻¹)⁻¹ ∈ A :=
                        (Subgroup.mem_normalizer_iff.mp hdAi t).1 htA
                      rcases ht with ⟨g,hg⟩
                      have htc : d⁻¹*t*(d⁻¹)⁻¹ =
                          (d⁻¹*g)*x*(d⁻¹*g)⁻¹ := by
                        rw [hg]
                        simp [mul_assoc]
                      rw [htc] at htAd ⊢
                      exact hclassN (d⁻¹*g) htAd.2
                  have hNNstrict : Subgroup.normalizer (I : Set G) <
                       Subgroup.normalizer (J : Set G) :=
                    lt_of_le_not_ge hNJ (by
                      intro hback
                      exact hdNIout (hback hdAJ))
                  have hJp : IsPGroup p J := IsPGroup.to_le hIp hJI
                  have hNJproper : Subgroup.normalizer (J : Set G) ≠
                      (⊤ : Subgroup G) :=
                    Foo.normalizer_ne_top_of_conj_mem_of_core_eq_bot
                      (by simpa [C] using hc0) hx1 J hJp a hyJ
                  have hallJ : ∀ W : Sylow p
                      (Subgroup.normalizer (J : Set G)),
                       (⟨a*x*a⁻¹, Subgroup.le_normalizer hyJ⟩ :
                         Subgroup.normalizer (J : Set G)) ∈ W :=
                    Foo.conj_mem_all_sylow_of_normalizer_of_core_eq_bot
                      (by simpa [C] using hc0) hx1 hproper J hJp a hyJ
                  -- The other side gives a second point of `N(J)` not in
                  -- `N(I)`, in its own Sylow.  We shall use both points; no
                  -- extension of a normalizer-Sylow is asserted contained in it.
                  let B : Subgroup G :=
                    (Q₁ : Subgroup G) ⊓ Subgroup.normalizer (I : Set G)
                  have hIB : I ≤ B := by
                    intro t ht
                    exact ⟨hIQ ht, Subgroup.le_normalizer ht⟩
                  have hBQ : B ≤ (Q₁ : Subgroup G) := inf_le_left
                  have hBne : B ≠ (Q₁ : Subgroup G) := by
                    intro he
                    apply hQout
                    intro t ht
                    have hb : t ∈ B := by rw [he]; exact ht
                    exact hb.2
                  obtain ⟨e, heQ, heB, heout⟩ :=
                    Foo.exists_mem_sylow_normalizer_not_mem Q₁ B hBQ hBne
                  have heNIout : e ∉ Subgroup.normalizer (I : Set G) := by
                    intro he
                    exact heout ⟨heQ, he⟩
                  have heBJ : e ∈ Subgroup.normalizer (J : Set G) := by
                    have heBn := Subgroup.mem_normalizer_iff.mp heB
                    apply Foo.mem_normalizer_closure_conj_of_preserves x I e
                    · intro t htI ht
                      have htB : t ∈ B := hIB htI
                      have hte : e*t*e⁻¹ ∈ B := (heBn t).1 htB
                      rcases ht with ⟨g,hg⟩
                      have heq : e*t*e⁻¹ = (e*g)*x*(e*g)⁻¹ := by
                        rw [hg]
                        simp [mul_assoc]
                      rw [heq] at hte ⊢
                      exact hclassN (e*g) hte.2
                    · intro t htI ht
                      have hein : e⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
                        (Subgroup.normalizer (B : Set G)).inv_mem heB
                      have htB : t ∈ B := hIB htI
                      have hte : e⁻¹*t*(e⁻¹)⁻¹ ∈ B :=
                        (Subgroup.mem_normalizer_iff.mp hein t).1 htB
                      rcases ht with ⟨g,hg⟩
                      have heq : e⁻¹*t*(e⁻¹)⁻¹ =
                          (e⁻¹*g)*x*(e⁻¹*g)⁻¹ := by
                        rw [hg]
                        simp [mul_assoc]
                      rw [heq] at hte ⊢
                      exact hclassN (e⁻¹*g) hte.2
                  have hINJ : I ≤ Subgroup.normalizer (J : Set G) :=
                    fun t ht => hNJ (Subgroup.le_normalizer ht)
                  -- If a normalizer-core element at the new level lay outside
                  -- the old intersection, extend along each side. Both
                  -- extensions contain the *whole normalizer part* of that
                  -- side. The witnesses d and e make each old intersection
                  -- strictly bigger, forcing opposite statuses for x.
                  have coreNJ_le_I :
                      Subgroup.map (Subgroup.normalizer (J : Set G)).subtype
                        (sSup {L : Subgroup
                           (Subgroup.normalizer (J : Set G)) |
                           L.Normal ∧ IsPGroup p L} :
                           Subgroup (Subgroup.normalizer (J : Set G))) ≤ I := by
                    intro z hz
                    rcases hz with ⟨w, hw, rfl⟩
                    have wzN : (w : G) ∈
                        Subgroup.normalizer (J : Set G) := w.property
                    have wall : ∀ Z : Sylow p
                        (Subgroup.normalizer (J : Set G)),
                        w ∈ Z :=
                      (Foo.mem_sup_core_iff_mem_all_sylow p w).1 hw
                    obtain ⟨S, hyS, hwS, hpartR⟩ :=
                      Foo.exists_sylow_containing_normalizer_part_two
                        R J (a*x*a⁻¹) hyJ hallJ (w : G) wzN wall
                    obtain ⟨T', hyT', hwT', hpartQ⟩ :=
                      Foo.exists_sylow_containing_normalizer_part_two
                        Q₁ J (a*x*a⁻¹) hyJ hallJ (w : G) wzN wall
                    have hIRSle : I ≤ ((R : Subgroup G) ⊓
                          (S : Subgroup G) : Subgroup G) := by
                      intro t ht
                      exact ⟨hIR ht, hpartR t (hIR ht) (hINJ ht)⟩
                    have hdSin : d ∈ (S : Subgroup G) :=
                      hpartR d hdR hdAJ
                    have hdIout : d ∉ I := by
                      intro ht
                      exact hdNIout (Subgroup.le_normalizer ht)
                    have hIRS : I < ((R : Subgroup G) ⊓
                          (S : Subgroup G) : Subgroup G) :=
                      lt_of_le_not_ge hIRSle (by
                        intro hback
                        exact hdIout (hback ⟨hdR, hdSin⟩))
                    have hxS' : x ∈ (S : Subgroup G) := by
                      by_contra hxo
                      have hb := hmax S a R hxo hxR hyR hyS
                      have hb' : Nat.card (((R : Subgroup G) ⊓
                          (S : Subgroup G) : Subgroup G)) ≤ Nat.card I := by
                        simpa [I] using hb
                      have hlt := Foo.natCard_subgroup_lt_of_lt hIRS
                      exact False.elim ((Nat.not_lt_of_ge hb') hlt)
                    have hIQTle : I ≤ ((Q₁ : Subgroup G) ⊓
                          (T' : Subgroup G) : Subgroup G) := by
                      intro t ht
                      exact ⟨hIQ ht, hpartQ t (hIQ ht) (hINJ ht)⟩
                    have heTin : e ∈ (T' : Subgroup G) :=
                      hpartQ e heQ heBJ
                    have heIout : e ∉ I := by
                      intro ht
                      exact heNIout (Subgroup.le_normalizer ht)
                    have hIQT : I < ((Q₁ : Subgroup G) ⊓
                          (T' : Subgroup G) : Subgroup G) :=
                      lt_of_le_not_ge hIQTle (by
                        intro hback
                        exact heIout (hback ⟨heQ, heTin⟩))
                    have hxTout : x ∉ (T' : Subgroup G) := by
                      intro hxin
                      have hb := hmax Q₁ a T' homit hxin hyT' hyQ
                      have hec : ((Q₁ : Subgroup G) ⊓
                          (T' : Subgroup G) : Subgroup G) =
                          ((T' : Subgroup G) ⊓
                          (Q₁ : Subgroup G) : Subgroup G) := inf_comm _ _
                      have hlt0 : Nat.card I < Nat.card
                          (((Q₁ : Subgroup G) ⊓
                            (T' : Subgroup G) : Subgroup G)) :=
                        Foo.natCard_subgroup_lt_of_lt hIQT
                      have hlt : Nat.card I < Nat.card
                          (((T' : Subgroup G) ⊓
                            (Q₁ : Subgroup G) : Subgroup G)) := by
                        simpa [hec] using hlt0
                      have hb' : Nat.card (((T' : Subgroup G) ⊓
                          (Q₁ : Subgroup G) : Subgroup G)) ≤ Nat.card I := by
                        simpa [I] using hb
                      exact (Nat.not_lt_of_ge hb') hlt
                    by_contra hwout0
                    have hwout : (w : G) ∉ I := hwout0
                    -- The two new extensions already violate maximality.
                    have hleST : I ≤ ((S : Subgroup G) ⊓
                          (T' : Subgroup G) : Subgroup G) := by
                      intro t ht
                      exact ⟨hpartR t (hIR ht) (hINJ ht),
                        hpartQ t (hIQ ht) (hINJ ht)⟩
                    have hltST : I < ((S : Subgroup G) ⊓
                          (T' : Subgroup G) : Subgroup G) :=
                      lt_of_le_not_ge hleST (by
                        intro hback
                        exact hwout (hback ⟨hwS, hwT'⟩))
                    have hb := hmax T' a S hxTout hxS' hyS hyT'
                    have hb' : Nat.card (((S : Subgroup G) ⊓
                          (T' : Subgroup G) : Subgroup G)) ≤ Nat.card I := by
                      simpa [I] using hb
                    have hlt := Foo.natCard_subgroup_lt_of_lt hltST
                    exact False.elim ((Nat.not_lt_of_ge hb') hlt)
                  have hclassNJ : ∀ (g : G),
                      g*x*g⁻¹ ∈ Subgroup.normalizer (J : Set G) →
                        g*x*g⁻¹ ∈ J := by
                    intro g hg
                    have hsup : (⟨g*x*g⁻¹, hg⟩ :
                        Subgroup.normalizer (J : Set G)) ∈
                        (sSup {L : Subgroup
                          (Subgroup.normalizer (J : Set G)) |
                          L.Normal ∧ IsPGroup p L} :
                          Subgroup (Subgroup.normalizer (J : Set G))) :=
                      Foo.conj_mem_sup_core_of_hproper hproper g
                        (Subgroup.normalizer (J : Set G)) hg hNJproper
                    have hm : g*x*g⁻¹ ∈
                        Subgroup.map (Subgroup.normalizer (J : Set G)).subtype
                          (sSup {L : Subgroup
                            (Subgroup.normalizer (J : Set G)) |
                            L.Normal ∧ IsPGroup p L} :
                            Subgroup (Subgroup.normalizer (J : Set G))) := by
                      refine ⟨⟨g*x*g⁻¹,hg⟩, hsup, rfl⟩
                    have hinto : g*x*g⁻¹ ∈ I := coreNJ_le_I hm
                    apply Subgroup.subset_closure
                    exact ⟨hinto, ⟨g, rfl⟩⟩
                  -- `J` is already generated by the class elements it
                  -- contains: every generator used in its definition lies in
                  -- J, whence the two sets of generators agree.
                  have hJJ : Subgroup.closure
                       ({t : G | t ∈ J ∧ ∃ g : G,
                          t = g*x*g⁻¹} : Set G) = J := by
                    apply le_antisymm
                    · apply (Subgroup.closure_le _).2
                      intro t ht
                      exact ht.1
                    · -- generators of J (those in I) are also in the smaller set
                      dsimp [J]
                      apply (Subgroup.closure_le _).2
                      intro t ht
                      apply Subgroup.subset_closure
                      refine ⟨?_, ht.2⟩
                      -- the same generator belongs to J
                      change t ∈ Subgroup.closure
                        ({u : G | u ∈ I ∧ ∃ g : G,
                          u = g*x*g⁻¹} : Set G)
                      exact Subgroup.subset_closure ht
                  have hRJNout : ¬ (R : Subgroup G) ≤
                        Subgroup.normalizer (J : Set G) := by
                    intro hle
                    have hxj := hclassNJ (1 : G) (by
                      simpa using (hle hxR))
                    have hxi : x ∈ I := by
                      have : (1:G)*x*(1:G)⁻¹ ∈ I := hJI hxj
                      simpa using this
                    exact homit (hIQ hxi)
                  let A' : Subgroup G :=
                      (R : Subgroup G) ⊓ Subgroup.normalizer (J : Set G)
                  have hIA' : J ≤ A' := by
                    intro t ht
                    exact ⟨hIR (hJI ht), Subgroup.le_normalizer ht⟩
                  have hA'R : A' ≤ (R : Subgroup G) := inf_le_left
                  have hA'ne : A' ≠ (R : Subgroup G) := by
                    intro he
                    apply hRJNout
                    intro t ht
                    have hh : t ∈ A' := by rw [he]; exact ht
                    exact hh.2
                  obtain ⟨f, hfR, hfA, hfout⟩ :=
                    Foo.exists_mem_sylow_normalizer_not_mem R A' hA'R hA'ne
                  have hfNJout : f ∉ Subgroup.normalizer (J : Set G) := by
                    intro hf
                    exact hfout ⟨hfR, hf⟩
                  -- But normalizing this Sylow part does normalize J.  This
                  -- is the impossible extra point in its normalizer.
                  have hfJJ : f ∈ Subgroup.normalizer
                         (Subgroup.closure ({t : G | t ∈ J ∧
                           ∃ g : G, t = g*x*g⁻¹} : Set G) : Set G) := by
                    have hfAn := Subgroup.mem_normalizer_iff.mp hfA
                    apply Foo.mem_normalizer_closure_conj_of_preserves x J f
                    · intro t htJ ht
                      have htA : t ∈ A' := hIA' htJ
                      have htf : f*t*f⁻¹ ∈ A' := (hfAn t).1 htA
                      rcases ht with ⟨g,hg⟩
                      have heq : f*t*f⁻¹ = (f*g)*x*(f*g)⁻¹ := by
                        rw [hg]
                        simp [mul_assoc]
                      rw [heq] at htf ⊢
                      exact hclassNJ (f*g) htf.2
                    · intro t htJ ht
                      have hfin : f⁻¹ ∈ Subgroup.normalizer (A' : Set G) :=
                        (Subgroup.normalizer (A' : Set G)).inv_mem hfA
                      have htA : t ∈ A' := hIA' htJ
                      have htf : f⁻¹*t*(f⁻¹)⁻¹ ∈ A' :=
                        (Subgroup.mem_normalizer_iff.mp hfin t).1 htA
                      rcases ht with ⟨g,hg⟩
                      have heq : f⁻¹*t*(f⁻¹)⁻¹ =
                          (f⁻¹*g)*x*(f⁻¹*g)⁻¹ := by
                        rw [hg]
                        simp [mul_assoc]
                      rw [heq] at htf ⊢
                      exact hclassNJ (f⁻¹*g) htf.2
                  apply hfNJout
                  rw [← hJJ]
                  exact hfJJ
              · exact hxQ
            · exact Foo.mem_sup_core_of_normal_subgroup p H0 hn0 x hx0
                (hproper H0 hx0 hgen)
      · have hm : Nat.card (G ⧸ C) < n := by
          rw [← hcard, ← C.index_eq_card, ← C.card_mul_index]
          have hi : 0 < C.index := by
            rw [C.index_eq_card]
            exact Nat.card_pos
          have hCgt : 1 < Nat.card C := (C.one_lt_card_iff_ne_bot).2 hc0
          have hmul := Nat.mul_lt_mul_of_pos_right hCgt hi
          simpa using hmul
        have hdesc : ∀ g' : G ⧸ C,
            IsPGroup p (Subgroup.closure
              ({(x:G ⧸ C), g' * (x:G ⧸ C) * g'⁻¹} : Set (G ⧸ C))) :=
          Foo.descend_pair_hyp_to_quotient x hyp
        have hxq : (x:G ⧸ C) ∈
            (sSup {N : Subgroup (G ⧸ C) | N.Normal ∧ IsPGroup p N} : Subgroup (G ⧸ C)) := by
          exact ih _ hm (x : G ⧸ C) hdesc rfl
        exact Foo.mem_sup_core_of_quotient p Cp x hxq
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
