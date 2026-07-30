import Mathlib

/-!
# Self-contained helpers for the Baer-Suzuki theorem

This file develops, on top of Mathlib, the minimal group-theoretic machinery
needed to state and prove the single-element form of the Baer-Suzuki theorem:

  `x ∈ O_p(G) ↔ ∀ g : G, ⟨x, g · x · g⁻¹⟩ is a p-group`

for a finite group `G` and a prime `p`. The proof structure follows
I. M. Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapters 1 and 2;
the deep direction routes through Baer's iff form (Thm 2.12) and Wielandt's
Zipper Lemma (Thm 2.9).

Original sources:

* R. Baer, *Engelsche Elemente Noetherscher Gruppen*, Math. Ann. **133** (1957),
  256-270 (the case `p = 2`).
* M. Suzuki, *Finite groups in which the centralizer of any element of order 2
  is 2-closed*, Ann. of Math. (2) **82** (1965), 191-212 (general `p`).
-/

namespace Submission.Helpers

open scoped Pointwise

variable {G : Type*} [Group G]

/-! ### `O_p(G)`: the `p`-core -/

/-- `O_p(G)`, defined as the intersection of all Sylow `p`-subgroups of `G`. -/
def opCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨅ P : Sylow p G, (P : Subgroup G)

@[simp]
theorem mem_opCore {p : ℕ} {x : G} :
    x ∈ opCore p G ↔ ∀ P : Sylow p G, x ∈ (P : Subgroup G) := by
  simp [opCore, Subgroup.mem_iInf]

theorem opCore_le {p : ℕ} (P : Sylow p G) : opCore p G ≤ (P : Subgroup G) :=
  iInf_le _ P

theorem opCore_isPGroup (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] :
    IsPGroup p (opCore p G) := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  exact P.2.of_injective (Subgroup.inclusion (opCore_le P))
    (Subgroup.inclusion_injective _)

instance opCore.normal (p : ℕ) (G : Type*) [Group G] : (opCore p G).Normal := by
  apply Subgroup.Normal.of_conjugate_fixed
  intro g
  ext x
  simp only [mem_opCore, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
  constructor
  · intro h P
    have hQ : (MulAut.conj g)⁻¹ x ∈ (↑(g⁻¹ • P) : Subgroup G) := h (g⁻¹ • P)
    rw [Sylow.coe_subgroup_smul, ← map_inv,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hQ
    simp only [map_inv, inv_inv, MulAut.smul_def] at hQ
    rwa [MulAut.apply_inv_self] at hQ
  · intro h P
    have hQ : x ∈ (↑(g • P) : Subgroup G) := h (g • P)
    rw [Sylow.coe_subgroup_smul,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hQ
    exact hQ

instance opCore.characteristic (p : ℕ) (G : Type*) [Group G] :
    (opCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_le_comap]
  intro φ x hx
  rw [Subgroup.mem_comap, mem_opCore]
  rw [mem_opCore] at hx
  intro Q
  have hinj : Function.Injective (φ.toMonoidHom : G →* G) := φ.injective
  have hrange : (Q : Subgroup G) ≤ (φ.toMonoidHom : G →* G).range := by
    rw [MonoidHom.range_eq_top.mpr φ.surjective]; exact le_top
  have hxQ' := hx (Q.comapOfInjective (φ.toMonoidHom : G →* G) hinj hrange)
  rwa [Sylow.coe_comapOfInjective, Subgroup.mem_comap] at hxQ'

/-- **Isaacs Problem 1B.2**. Any normal `p`-subgroup is contained in `O_p(G)`. -/
theorem normal_pgroup_le_opCore {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite (Sylow p G)]
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p N) :
    N ≤ opCore p G := by
  rw [opCore, le_iInf_iff]
  intro P
  obtain ⟨Q, hNQ⟩ := hN.exists_le_sylow
  obtain ⟨g, hgQ⟩ := MulAction.exists_smul_eq G Q P
  calc (N : Subgroup G)
      = MulAut.conj g • N := (Subgroup.Normal.conj_smul_eq_self g N).symm
    _ ≤ MulAut.conj g • (Q : Subgroup G) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hNQ
    _ = ↑(g • Q) := Sylow.coe_subgroup_smul.symm
    _ = ↑P := by rw [hgQ]

/-- **Isaacs Thm 1.26 (1) ⇔ (4)**. A finite group is nilpotent iff every Sylow
subgroup is normal. -/
theorem isNilpotent_iff_forall_sylow_normal [Finite G] :
    Group.IsNilpotent G ↔
      ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G), (↑P : Subgroup G).Normal :=
  isNilpotent_of_finite_tfae.out 0 3

theorem Sylow.normal_of_isNilpotent [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) : (↑P : Subgroup G).Normal :=
  isNilpotent_iff_forall_sylow_normal.mp ‹_› p P

/-! ### `F(G)`: the Fitting subgroup -/

/-- **Fitting subgroup** `F(G)`: the supremum of `O_p(G)` over all primes `p`.
By Isaacs Cor 1.28 this is the largest normal nilpotent subgroup of `G`. -/
def fitting (G : Type*) [Group G] : Subgroup G :=
  ⨆ p : Nat.Primes, opCore (p : ℕ) G

theorem opCore_le_fitting (p : Nat.Primes) (G : Type*) [Group G] :
    opCore (p : ℕ) G ≤ fitting G :=
  le_iSup (fun q : Nat.Primes => opCore (q : ℕ) G) p

instance fitting.characteristic (G : Type*) [Group G] : (fitting G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  change (⨆ p : Nat.Primes, opCore (p : ℕ) G).map φ.toMonoidHom
    = ⨆ p : Nat.Primes, opCore (p : ℕ) G
  rw [Subgroup.map_iSup]
  exact iSup_congr fun _ =>
    Subgroup.characteristic_iff_map_eq.mp (opCore.characteristic _ _) φ

instance fitting.normal (G : Type*) [Group G] : (fitting G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => g * x * g⁻¹ ∈ fitting G) hn
    ?mem ?one ?mul
  case mem =>
    intro p x hx
    exact (opCore_le_fitting p G) ((opCore.normal (p : ℕ) G).conj_mem x hx g)
  case one =>
    simp
  case mul =>
    intro x y hx hy
    have heq : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [heq]
    exact (fitting G).mul_mem hx hy

private theorem iSup_default_sylow_eq_top_of_nilpotent
    (N : Type*) [Group N] [Finite N] [Group.IsNilpotent N] :
    ⨆ p : (Nat.card N).primeFactors,
        ((default : Sylow (p : ℕ) N) : Subgroup N) = ⊤ := by
  classical
  have hnormal : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p N), P.Normal := fun P =>
    Sylow.normal_of_isNilpotent P
  have _ := Fintype.ofFinite N
  set ps := (Nat.card N).primeFactors with hps
  let P : ∀ p, Sylow p N := default
  have hPfin : ∀ p, Fintype (P p) := fun p ↦ Fintype.ofFinite (P p)
  have hcomm : Pairwise fun p₁ p₂ : ps =>
      ∀ x y : N, x ∈ (P p₁ : Subgroup N) → y ∈ (P p₂ : Subgroup N) → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    haveI hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (hnormal (P p₁)) (hnormal (P p₂))
    exact IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  set f := Subgroup.noncommPiCoprod (G := N) (H := fun p : ps => (P p : Subgroup N)) hcomm
    with hf
  have hinj : Function.Injective f := by
    apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply Subgroup.independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' := Fact.mk (Nat.prime_of_mem_primeFactors hp₁)
    haveI hp₂' := Fact.mk (Nat.prime_of_mem_primeFactors hp₂)
    have hne' : p₁ ≠ p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    exact IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _ (P p₁).isPGroup' (P p₂).isPGroup'
  have hcard : Fintype.card (∀ p : ps, P p) = Fintype.card N := by
    simp only [← Nat.card_eq_fintype_card]
    calc Nat.card (∀ p : ps, P p)
        = ∏ p : ps, Nat.card (P p) := Nat.card_pi
      _ = ∏ p : ps, p.1 ^ (Nat.card N).factorization p.1 := by
          refine Finset.prod_congr rfl ?_
          rintro ⟨p, hp⟩ _
          exact @Sylow.card_eq_multiplicity _ _ _ p
            ⟨Nat.prime_of_mem_primeFactors hp⟩ (P p)
      _ = ∏ p ∈ ps, p ^ (Nat.card N).factorization p :=
          Finset.prod_finset_coe (fun p => p ^ (Nat.card N).factorization p) _
      _ = (Nat.card N).factorization.prod (· ^ ·) := rfl
      _ = Nat.card N := Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  have hrange : f.range = (⊤ : Subgroup N) :=
    MonoidHom.range_eq_top.mpr hbij.surjective
  have hrange' : f.range = ⨆ p : ps, (P p : Subgroup N) :=
    Subgroup.noncommPiCoprod_range
  rw [hrange'] at hrange
  exact hrange

/-- **Isaacs Cor 1.28(b)**. Any normal nilpotent subgroup is contained in `F(G)`. -/
theorem nilpotent_normal_le_fitting [Finite G] {N : Subgroup G} [N.Normal]
    [Group.IsNilpotent N] : N ≤ fitting G := by
  have hsup : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hsup, ← iSup_default_sylow_eq_top_of_nilpotent N, Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨p, hp⟩
  haveI hp' : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  have hPN : (default : Sylow p N).Normal := Sylow.normal_of_isNilpotent _
  haveI : ((default : Sylow p N) : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal _ hPN
  haveI : (((default : Sylow p N) : Subgroup N).map N.subtype).Normal :=
    inferInstance
  have hpGroup : IsPGroup p (((default : Sylow p N) : Subgroup N).map N.subtype) :=
    (default : Sylow p N).2.map N.subtype
  calc ((default : Sylow p N) : Subgroup N).map N.subtype
      ≤ opCore p G := normal_pgroup_le_opCore hpGroup
    _ ≤ fitting G := opCore_le_fitting ⟨p, hp'.out⟩ G

theorem opCore_eq_bot_of_not_mem_primeFactors [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : p ∉ (Nat.card G).primeFactors) :
    opCore p G = ⊥ := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
  have hcard : Nat.card (P : Subgroup G) = 1 := by
    rw [Sylow.card_eq_multiplicity P]
    have hfact : (Nat.card G).factorization p = 0 := by
      by_cases hdvd : p ∣ Nat.card G
      · exfalso
        exact hp (Nat.mem_primeFactors.mpr
          ⟨(Fact.out : p.Prime), hdvd, Nat.card_pos.ne'⟩)
      · exact Nat.factorization_eq_zero_of_not_dvd hdvd
    rw [hfact, pow_zero]
  have hPbot : (P : Subgroup G) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  exact le_bot_iff.mp (le_of_le_of_eq (opCore_le P) hPbot)

theorem fitting_eq_iSup_primeFactors [Finite G] :
    fitting G = ⨆ p : (Nat.card G).primeFactors, opCore (p : ℕ) G := by
  apply le_antisymm
  · refine iSup_le (fun p => ?_)
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    by_cases hmem : (p : ℕ) ∈ (Nat.card G).primeFactors
    · exact le_iSup (fun q : (Nat.card G).primeFactors => opCore (q : ℕ) G) ⟨p, hmem⟩
    · rw [opCore_eq_bot_of_not_mem_primeFactors hmem]
      exact bot_le
  · refine iSup_le (fun p => ?_)
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    exact opCore_le_fitting ⟨(p : ℕ), hp⟩ G

/-- **Isaacs Cor 1.28(a)**. `F(G)` is nilpotent. -/
instance fitting.isNilpotent [Finite G] : Group.IsNilpotent (fitting G) := by
  classical
  have _ := Fintype.ofFinite G
  set ps := (Nat.card G).primeFactors with hps
  have hcomm : Pairwise fun p₁ p₂ : ps =>
      ∀ x y : G, x ∈ opCore (p₁ : ℕ) G → y ∈ opCore (p₂ : ℕ) G → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' : Fact (p₁ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₁⟩
    haveI hp₂' : Fact (p₂ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₂⟩
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (opCore.normal p₁ G)
      (opCore.normal p₂ G)
    exact IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _
      (opCore_isPGroup p₁ G) (opCore_isPGroup p₂ G)
  set f := Subgroup.noncommPiCoprod (G := G)
    (H := fun p : ps => opCore (p : ℕ) G) hcomm with hf
  have hinj : Function.Injective f := by
    apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
    apply Subgroup.independent_of_coprime_order hcomm
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    haveI hp₁' : Fact (p₁ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₁⟩
    haveI hp₂' : Fact (p₂ : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hp₂⟩
    have hne' : p₁ ≠ p₂ := by simpa using hne
    simp only [← Nat.card_eq_fintype_card]
    exact IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _
      (opCore_isPGroup p₁ G) (opCore_isPGroup p₂ G)
  have hrange : f.range = fitting G := by
    rw [hf, Subgroup.noncommPiCoprod_range, ← fitting_eq_iSup_primeFactors]
  let e : (∀ p : ps, opCore (p : ℕ) G) ≃* fitting G :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hnilp : ∀ p : ps, Group.IsNilpotent (opCore (p : ℕ) G) := by
    rintro ⟨p, hp⟩
    haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    exact (opCore_isPGroup p G).isNilpotent
  haveI : ∀ p : ps, Group.IsNilpotent (opCore (p : ℕ) G) := hnilp
  haveI : Group.IsNilpotent (∀ p : ps, opCore (p : ℕ) G) := isNilpotent_pi
  exact nilpotent_of_mulEquiv e

/-! ### Subnormality basics -/

/-- **Isaacs Lemma 2.1**, hard direction: in a nilpotent finite group, every
subgroup is subnormal. -/
theorem isSubnormal_of_isNilpotent_finite [Finite G] [Group.IsNilpotent G]
    (H : Subgroup G) : H.IsSubnormal := by
  classical
  induction hN : H.index using Nat.strong_induction_on generalizing H with
  | _ n ih =>
    by_cases hHt : H = ⊤
    · rw [hHt]; exact Subgroup.IsSubnormal.top
    · have hNC : NormalizerCondition G :=
        ((isNilpotent_of_finite_tfae (G := G)).out 0 1).mp ‹_›
      have hHlt : H < ⊤ := lt_top_iff_ne_top.mpr hHt
      have hH_lt_N : H < Subgroup.normalizer (H : Set G) := hNC H hHlt
      have hidx : (Subgroup.normalizer (H : Set G)).index < n := by
        rw [← hN]
        exact Subgroup.index_strictAnti hH_lt_N
      have hSubnN : (Subgroup.normalizer (H : Set G)).IsSubnormal :=
        ih _ hidx _ rfl
      have hNorm : (H.subgroupOf (Subgroup.normalizer (H : Set G))).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.le_normalizer)).mpr le_rfl
      exact Subgroup.IsSubnormal.step _ _ Subgroup.le_normalizer hSubnN hNorm

/-- **Isaacs Lemma 2.7**: if `M, N ◁ G` and `M ∩ N = 1` then elements of `M`
and `N` commute. -/
theorem commute_of_disjoint_normal {M N : Subgroup G} [hM : M.Normal] [hN : N.Normal]
    (hDis : Disjoint M N) {m n : G} (hm : m ∈ M) (hn : n ∈ N) : Commute m n :=
  Subgroup.commute_of_normal_of_disjoint M N hM hN hDis m n hm hn

/-! ### Minimal normal subgroups and the socle -/

/-- **Minimal normal subgroup**: a non-trivial normal subgroup with no
proper non-trivial `G`-normal subgroup. -/
def IsMinimalNormal (M : Subgroup G) : Prop :=
  M.Normal ∧ M ≠ ⊥ ∧ ∀ N : Subgroup G, N.Normal → N ≤ M → N = ⊥ ∨ N = M

variable (G) in
/-- **Socle** `Soc(G)`: the supremum of all minimal normal subgroups of `G`. -/
def socle : Subgroup G :=
  ⨆ M : {M : Subgroup G // IsMinimalNormal M}, (M : Subgroup G)

theorem isMinimalNormal_le_socle {M : Subgroup G} (hM : IsMinimalNormal M) :
    M ≤ socle G :=
  le_iSup (fun M : {M : Subgroup G // IsMinimalNormal M} => (M : Subgroup G)) ⟨M, hM⟩

instance socle.normal : (socle G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.iSup_induction _ (C := fun x => g * x * g⁻¹ ∈ socle G) hn
    ?mem ?one ?mul
  case mem =>
    rintro ⟨M, hM⟩ x hx
    exact isMinimalNormal_le_socle hM (hM.1.conj_mem x hx g)
  case one => simp
  case mul =>
    intro x y hx hy
    have heq : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [heq]
    exact (socle G).mul_mem hx hy

theorem IsMinimalNormal.map_equiv {M : Subgroup G} (hM : IsMinimalNormal M) (ϕ : G ≃* G) :
    IsMinimalNormal (M.map ϕ.toMonoidHom) := by
  refine ⟨hM.1.map ϕ.toMonoidHom ϕ.surjective, ?_, ?_⟩
  · intro heq
    apply hM.2.1
    rw [eq_bot_iff]
    intro m hm
    have hmem : ϕ m ∈ M.map ϕ.toMonoidHom := ⟨m, hm, rfl⟩
    rw [heq, Subgroup.mem_bot] at hmem
    have h1 : m = 1 := ϕ.injective (by rw [hmem]; exact (ϕ.map_one).symm)
    rw [h1]; exact Subgroup.one_mem _
  · intro N hN hNle
    have hN' : (N.map ϕ.symm.toMonoidHom).Normal := hN.map ϕ.symm.toMonoidHom ϕ.symm.surjective
    have hle : N.map ϕ.symm.toMonoidHom ≤ M := by
      rintro _ ⟨y, hyN, rfl⟩
      rcases hNle hyN with ⟨z, hzM, hzeq⟩
      have h1 : ϕ.symm.toMonoidHom y = z := by
        change ϕ.symm y = z
        rw [← hzeq]; exact ϕ.symm_apply_apply z
      rw [h1]; exact hzM
    have hback : (N.map ϕ.symm.toMonoidHom).map ϕ.toMonoidHom = N := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id N
      ext x; simp
    rcases hM.2.2 _ hN' hle with hbot | htop
    · left
      rw [← hback, hbot, Subgroup.map_bot]
    · right
      rw [← hback, htop]

instance socle.characteristic : (socle G).Characteristic := by
  refine (Subgroup.characteristic_iff_map_le).mpr ?_
  intro ϕ
  change (⨆ M : {M : Subgroup G // IsMinimalNormal M}, (M : Subgroup G)).map
      ϕ.toMonoidHom ≤ socle G
  rw [Subgroup.map_iSup]
  refine iSup_le ?_
  rintro ⟨M, hM⟩
  exact isMinimalNormal_le_socle (hM.map_equiv ϕ)

theorem exists_isMinimalNormal_le_of_normal [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) : ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ N := by
  classical
  suffices h : ∀ (k : ℕ) (N : Subgroup G), N.Normal → Nat.card N ≤ k → N ≠ ⊥ →
      ∃ M : Subgroup G, IsMinimalNormal M ∧ M ≤ N by
    exact h (Nat.card N) N ‹N.Normal› le_rfl hN
  intro k
  induction k with
  | zero =>
    intro N _ hcard _
    exact absurd (Nat.le_zero.mp hcard) Nat.card_pos.ne'
  | succ k ih =>
    intro N hNn hcard hNne
    by_cases hmin : ∀ K : Subgroup G, K.Normal → K ≤ N → K = ⊥ ∨ K = N
    · exact ⟨N, ⟨hNn, hNne, hmin⟩, le_rfl⟩
    · push Not at hmin
      obtain ⟨K, hKnorm, hKleN, hKne_bot, hKne_N⟩ := hmin
      have hKlt : K < N := lt_of_le_of_ne hKleN hKne_N
      have hsub : (K : Set G) ⊂ (N : Set G) := SetLike.coe_ssubset_coe.mpr hKlt
      obtain ⟨x, hxN, hxK⟩ := Set.exists_of_ssubset hsub
      have hcard_K : Nat.card K < Nat.card N := by
        have hequiv : K ≃ {n : N // (n : G) ∈ K} :=
          { toFun := fun ⟨g, hg⟩ => ⟨⟨g, hKleN hg⟩, hg⟩
            invFun := fun ⟨⟨g, _⟩, hg⟩ => ⟨g, hg⟩
            left_inv := fun ⟨_, _⟩ => rfl
            right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
        rw [Nat.card_congr hequiv]
        exact Finite.card_subtype_lt (p := fun n : N => (n : G) ∈ K)
          (x := ⟨x, hxN⟩) hxK
      have hcard_K_le : Nat.card K ≤ k := by omega
      obtain ⟨M, hMmin, hMleK⟩ := ih K hKnorm hcard_K_le hKne_bot
      exact ⟨M, hMmin, hMleK.trans hKleN⟩

/-! ### Isaacs Thm 2.2 (`H ≤ F(G) ⇔ nilpotent ∧ subnormal`) -/

private theorem le_fitting_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {H : Subgroup G},
      Group.IsNilpotent H → H.IsSubnormal → H ≤ fitting G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _ _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ H hNilp hSn
    by_cases hHtop : H = ⊤
    · subst hHtop
      haveI := hNilp
      exact nilpotent_normal_le_fitting
    · obtain ⟨K, hKnorm, hHK, hKlt⟩ := hSn.exists_normal_and_le_and_lt_top_of_ne hHtop
      have _ := hKnorm
      have hKcard_le : Nat.card K ≤ n := by
        have hKle : Nat.card K ≤ Nat.card G := K.card_le_card_group
        have hKne_top : K ≠ ⊤ := hKlt.ne
        have hKne : Nat.card K ≠ Nat.card G := fun heq =>
          hKne_top (Subgroup.eq_top_of_card_eq K heq)
        omega
      have hH_sn_in_K : (H.subgroupOf K).IsSubnormal := hSn.subgroupOf
      have hH_nilp_in_K : Group.IsNilpotent (H.subgroupOf K) :=
        nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHK).symm
      have hH_le_fitK : H.subgroupOf K ≤ fitting K :=
        ih K hKcard_le hH_nilp_in_K hH_sn_in_K
      have hHeq : (H.subgroupOf K).map K.subtype = H :=
        Subgroup.map_subgroupOf_eq_of_le hHK
      have hpush : H ≤ (fitting K).map K.subtype := by
        rw [← hHeq]; exact Subgroup.map_mono hH_le_fitK
      haveI : ((fitting K).map K.subtype).Normal := inferInstance
      haveI : Group.IsNilpotent ((fitting K).map K.subtype) :=
        nilpotent_of_mulEquiv ((fitting K).equivMapOfInjective K.subtype K.subtype_injective)
      exact hpush.trans nilpotent_normal_le_fitting

/-- **Isaacs Thm 2.2**. `H ≤ F(G) ↔ H` is nilpotent and subnormal. -/
theorem le_fitting_iff_isNilpotent_and_isSubnormal [Finite G] (H : Subgroup G) :
    H ≤ fitting G ↔ Group.IsNilpotent H ∧ H.IsSubnormal := by
  refine ⟨fun hH => ⟨?_, ?_⟩,
    fun ⟨hNilp, hSn⟩ => le_fitting_aux (Nat.card G) G le_rfl hNilp hSn⟩
  · exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hH)
  · have hFsn : (fitting G).IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
    have hHsn_in_F : (H.subgroupOf (fitting G)).IsSubnormal :=
      isSubnormal_of_isNilpotent_finite _
    exact Subgroup.IsSubnormal.trans hH hHsn_in_F hFsn

/-! ### Isaacs Thm 2.6 (minimal normal normalises any subnormal) -/

private theorem isMinimalNormal_le_normalizer_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {S M : Subgroup G}, S.IsSubnormal → IsMinimalNormal M →
      M ≤ Subgroup.normalizer (S : Set G) := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _ _ _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ hG S M hS hM
    classical
    have _ : M.Normal := hM.1
    by_cases hStop : S = ⊤
    · subst hStop
      rw [Subgroup.normalizer_eq_top (⊤ : Subgroup G)]
      exact le_top
    · obtain ⟨N, hNnorm, hSleN, hNlt⟩ := hS.exists_normal_and_le_and_lt_top_of_ne hStop
      have _ := hNnorm
      by_cases hMN : M ⊓ N = ⊥
      · intro m hm
        rw [Subgroup.mem_normalizer_iff]
        intro s
        constructor
        · intro hsS
          have hsN : s ∈ N := hSleN hsS
          have hcomm : Commute m s := commute_of_disjoint_normal
            (M := M) (N := N) (disjoint_iff.mpr hMN) hm hsN
          have hmsm : m * s * m⁻¹ = s := by
            rw [Commute.eq hcomm, mul_inv_cancel_right]
          rw [hmsm]; exact hsS
        · intro hmsm
          have hsN : m * s * m⁻¹ ∈ N := hSleN hmsm
          have hm_inv : m⁻¹ ∈ M := M.inv_mem hm
          have hcomm : Commute m⁻¹ (m * s * m⁻¹) := commute_of_disjoint_normal
            (M := M) (N := N) (disjoint_iff.mpr hMN) hm_inv hsN
          have hseq : s = m⁻¹ * (m * s * m⁻¹) * m := by group
          rw [hseq, Commute.eq hcomm, mul_assoc, inv_mul_cancel, mul_one]
          exact hmsm
      · have hMN_le_M : M ⊓ N ≤ M := inf_le_left
        haveI hMN_norm : (M ⊓ N).Normal := Subgroup.normal_inf_normal M N
        have hMN_eq_M : M ⊓ N = M := by
          rcases hM.2.2 (M ⊓ N) hMN_norm hMN_le_M with h | h
          · exact absurd h hMN
          · exact h
        have hMleN : M ≤ N := by
          have h : M ≤ M ⊓ N := le_of_eq hMN_eq_M.symm
          exact (le_inf_iff.mp h).2
        have hN_ne_top : N ≠ ⊤ := hNlt.ne
        obtain ⟨g, hg⟩ : ∃ g : G, g ∉ N := by
          by_contra h
          push Not at h
          exact hN_ne_top (eq_top_iff.mpr fun x _ => h x)
        have hN_card_lt : Nat.card N < Nat.card G :=
          Finite.card_subtype_lt (p := fun x : G => x ∈ N) (x := g) hg
        have hN_card_le_n : Nat.card N ≤ n := by omega
        have hNne_bot : N ≠ ⊥ := by
          intro h
          apply hM.2.1
          rw [eq_bot_iff]; rw [h] at hMleN; exact hMleN
        haveI hNNontriv : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNne_bot
        have hSsubN_sn : (S.subgroupOf N).IsSubnormal := hS.subgroupOf
        have hIH : ∀ K : Subgroup N, IsMinimalNormal K →
            K ≤ Subgroup.normalizer (S.subgroupOf N : Set N) := by
          intro K hK
          exact ih N hN_card_le_n hSsubN_sn hK
        have hSoc_le_norm_inner : socle N ≤ Subgroup.normalizer (S.subgroupOf N : Set N) := by
          refine iSup_le ?_
          rintro ⟨K, hK⟩
          exact hIH K hK
        have hSoc_lift_le_norm :
            (socle N).map N.subtype ≤ Subgroup.normalizer (S : Set G) := by
          rintro _ ⟨⟨g', hg'N⟩, hg'soc, rfl⟩
          change (g' : G) ∈ Subgroup.normalizer (S : Set G)
          have hg'norm : (⟨g', hg'N⟩ : N) ∈
              Subgroup.normalizer (S.subgroupOf N : Set N) := hSoc_le_norm_inner hg'soc
          rw [Subgroup.mem_normalizer_iff] at hg'norm ⊢
          intro s
          by_cases hsN : s ∈ N
          · have hpair := hg'norm ⟨s, hsN⟩
            constructor
            · intro hsS
              have h1 : (⟨s, hsN⟩ : N) ∈ S.subgroupOf N := by
                rwa [Subgroup.mem_subgroupOf]
              have h2 := hpair.mp h1
              rw [Subgroup.mem_subgroupOf] at h2
              convert h2 using 1
            · intro hgsg
              have hgsg_N : g' * s * g'⁻¹ ∈ N := hNnorm.conj_mem s hsN g'
              have h1 : (⟨g' * s * g'⁻¹, hgsg_N⟩ : N) ∈ S.subgroupOf N := by
                rwa [Subgroup.mem_subgroupOf]
              have hcong : (⟨g' * s * g'⁻¹, hgsg_N⟩ : N) =
                  ⟨g', hg'N⟩ * ⟨s, hsN⟩ * ⟨g', hg'N⟩⁻¹ := by
                apply Subtype.ext
                change g' * s * g'⁻¹ = (↑(⟨g', hg'N⟩ * ⟨s, hsN⟩ * ⟨g', hg'N⟩⁻¹ : N) : G)
                push_cast
                rfl
              rw [hcong] at h1
              have h2 := hpair.mpr h1
              rwa [Subgroup.mem_subgroupOf] at h2
          · have hgsg_notN : g' * s * g'⁻¹ ∉ N := by
              intro h
              apply hsN
              have hseq : s = g'⁻¹ * (g' * s * g'⁻¹) * g' := by group
              rw [hseq]
              have h' : g'⁻¹ * (g' * s * g'⁻¹) * (g'⁻¹)⁻¹ ∈ N :=
                hNnorm.conj_mem _ h g'⁻¹
              rwa [inv_inv] at h'
            constructor
            · intro hsS; exact absurd (hSleN hsS) hsN
            · intro hgsg; exact absurd (hSleN hgsg) hgsg_notN
        haveI hMsubN_norm : (M.subgroupOf N).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hMleN).mpr
            Subgroup.le_normalizer_of_normal
        have hMsubN_ne_bot : M.subgroupOf N ≠ ⊥ := by
          intro heq
          apply hM.2.1
          have hM_eq : M = (M.subgroupOf N).map N.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hMleN).symm
          rw [hM_eq, heq, Subgroup.map_bot]
        obtain ⟨K, hKmin, hKle⟩ :=
          exists_isMinimalNormal_le_of_normal (G := N) (M.subgroupOf N) hMsubN_ne_bot
        have hK_le_socN : K ≤ socle N := isMinimalNormal_le_socle hKmin
        have hKmap_le_M : K.map N.subtype ≤ M := by
          rintro _ ⟨k, hk, rfl⟩
          have := hKle hk
          rwa [Subgroup.mem_subgroupOf] at this
        have hKmap_le_socMap : K.map N.subtype ≤ (socle N).map N.subtype :=
          Subgroup.map_mono hK_le_socN
        have hKmap_ne_bot : K.map N.subtype ≠ ⊥ := by
          intro heq
          apply hKmin.2.1
          rw [eq_bot_iff]
          intro k hk
          have hmem : (k : G) ∈ K.map N.subtype := ⟨k, hk, rfl⟩
          rw [heq, Subgroup.mem_bot] at hmem
          have : k = 1 := Subtype.ext hmem
          rw [this]; exact Subgroup.one_mem _
        haveI hSocLift_normal : ((socle N).map N.subtype).Normal := inferInstance
        haveI hM_inf_norm : (M ⊓ (socle N).map N.subtype).Normal :=
          Subgroup.normal_inf_normal _ _
        have hM_inf_ne_bot : M ⊓ (socle N).map N.subtype ≠ ⊥ := by
          intro heq
          apply hKmap_ne_bot
          rw [eq_bot_iff]
          exact (le_inf hKmap_le_M hKmap_le_socMap).trans heq.le
        have hM_inf_eq_M : M ⊓ (socle N).map N.subtype = M := by
          rcases hM.2.2 _ hM_inf_norm inf_le_left with h | h
          · exact absurd h hM_inf_ne_bot
          · exact h
        have hM_le_SocLift : M ≤ (socle N).map N.subtype := by
          intro m hm
          have hmem : m ∈ M ⊓ (socle N).map N.subtype := by rw [hM_inf_eq_M]; exact hm
          exact hmem.2
        exact hM_le_SocLift.trans hSoc_lift_le_norm

/-- **Isaacs Thm 2.6**. Any minimal normal subgroup normalises any subnormal subgroup. -/
theorem isMinimalNormal_le_normalizer_of_isSubnormal [Finite G]
    {S M : Subgroup G} (hS : S.IsSubnormal) (hM : IsMinimalNormal M) :
    M ≤ Subgroup.normalizer (S : Set G) :=
  isMinimalNormal_le_normalizer_aux (Nat.card G) G le_rfl hS hM

/-! ### Isaacs Thm 2.5 (Wielandt's join theorem) -/

private theorem isSubnormal_sup_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {S T : Subgroup G}, S.IsSubnormal → T.IsSubnormal →
      (S ⊔ T).IsSubnormal := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _ _ _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ hG S T hS hT
    classical
    by_cases hGnontriv : Nontrivial G
    case neg =>
      rw [not_nontrivial_iff_subsingleton] at hGnontriv
      haveI := hGnontriv
      have hST_top : (S ⊔ T : Subgroup G) = ⊤ := by
        refine eq_top_iff.mpr (fun x _ => ?_)
        rw [show x = 1 from Subsingleton.elim x 1]
        exact (S ⊔ T).one_mem
      rw [hST_top]
      exact Subgroup.IsSubnormal.top
    case pos =>
      haveI := hGnontriv
      have htop_ne_bot : (⊤ : Subgroup G) ≠ ⊥ := by
        intro h
        obtain ⟨x, y, hxy⟩ := hGnontriv
        apply hxy
        have hxbot : x ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top x
        have hybot : y ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_top y
        rw [Subgroup.mem_bot] at hxbot hybot
        rw [hxbot, hybot]
      obtain ⟨M, hM, _⟩ :=
        exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) htop_ne_bot
      haveI hMnorm : M.Normal := hM.1
      let f : G →* G ⧸ M := QuotientGroup.mk' M
      have hSbar : (S.map f).IsSubnormal := hS.map (QuotientGroup.mk'_surjective M)
      have hTbar : (T.map f).IsSubnormal := hT.map (QuotientGroup.mk'_surjective M)
      have h1lt_M : 1 < Nat.card M := by
        have h_ne_one : Nat.card M ≠ 1 := by
          intro h1
          apply hM.2.1
          haveI hSub : Subsingleton M := Nat.card_eq_one_iff_unique.mp h1 |>.1
          refine eq_bot_iff.mpr (fun x hx => ?_)
          rw [Subgroup.mem_bot]
          exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : M) 1)
        have h_pos : 0 < Nat.card M := Nat.card_pos
        omega
      have hquot_lt : Nat.card (G ⧸ M) < Nat.card G := by
        have heq : M.index * Nat.card M = Nat.card G := M.index_mul_card
        have hM_pos : 0 < Nat.card M := Nat.card_pos
        have hidx_eq : M.index = Nat.card G / Nat.card M := by
          rw [← heq, Nat.mul_div_cancel _ hM_pos]
        change M.index < Nat.card G
        rw [hidx_eq]
        exact Nat.div_lt_self Nat.card_pos h1lt_M
      have hquot_le : Nat.card (G ⧸ M) ≤ n := by omega
      have hIH : (S.map f ⊔ T.map f).IsSubnormal :=
        ih (G ⧸ M) hquot_le hSbar hTbar
      rw [← Subgroup.map_sup] at hIH
      have hcomap_subn : (((S ⊔ T).map f).comap f).IsSubnormal := hIH.comap f
      have hcomap_eq : ((S ⊔ T).map f).comap f = (S ⊔ T) ⊔ M := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      rw [hcomap_eq] at hcomap_subn
      have hMS : M ≤ Subgroup.normalizer (S : Set G) :=
        isMinimalNormal_le_normalizer_of_isSubnormal hS hM
      have hMT : M ≤ Subgroup.normalizer (T : Set G) :=
        isMinimalNormal_le_normalizer_of_isSubnormal hT hM
      have hMnormST : M ≤ Subgroup.normalizer ((S ⊔ T : Subgroup G) : Set G) :=
        (le_inf hMS hMT).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup S T)
      have hSupSup_le_norm :
          (S ⊔ T) ⊔ M ≤ Subgroup.normalizer ((S ⊔ T : Subgroup G) : Set G) :=
        sup_le Subgroup.le_normalizer hMnormST
      have hSupNormal : ((S ⊔ T).subgroupOf ((S ⊔ T) ⊔ M)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hSupSup_le_norm
      exact Subgroup.IsSubnormal.step _ _ le_sup_left hcomap_subn hSupNormal

/-- **Isaacs Thm 2.5** (Wielandt's join theorem). The supremum of two subnormal
subgroups is subnormal. -/
theorem isSubnormal_sup_of_isSubnormal [Finite G] {S T : Subgroup G}
    (hS : S.IsSubnormal) (hT : T.IsSubnormal) : (S ⊔ T).IsSubnormal :=
  isSubnormal_sup_aux (Nat.card G) G le_rfl hS hT

/-! ### Wielandt's Zipper Lemma (Isaacs Thm 2.9) -/

/-- **Wielandt's Zipper Lemma** (Isaacs Thm 2.9). If `S ≤ G` is such that the
embedding `S.subgroupOf H` is subnormal for every proper subgroup `H ⊃ S`, but
`S` is not subnormal in `G`, then there is a unique maximal subgroup of `G`
containing `S`. -/
theorem zipper_lemma [Finite G] {S : Subgroup G}
    (hS_proper : ∀ H : Subgroup G, S ≤ H → H ≠ ⊤ → (S.subgroupOf H).IsSubnormal)
    (hS_not_sn : ¬ S.IsSubnormal) :
    ∃ M : Subgroup G, IsCoatom M ∧ S ≤ M ∧
      ∀ K : Subgroup G, IsCoatom K → S ≤ K → K = M := by
  classical
  induction hIdx : S.index using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    have hS_idx_pos : 0 < S.index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rcases Nat.lt_or_ge 1 n with hgt | hle
    swap
    · have hn_eq : n = 1 := by
        have hn_pos : 0 < n := hIdx ▸ hS_idx_pos
        omega
      have hS_top : S = ⊤ := Subgroup.index_eq_one.mp (hIdx.trans hn_eq)
      exact absurd (hS_top ▸ Subgroup.IsSubnormal.top) hS_not_sn
    · have hS_not_normal : ¬ S.Normal := fun hN => hS_not_sn hN.isSubnormal
      have hN_lt_top : Subgroup.normalizer (S : Set G) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro hN_top
        exact hS_not_normal (Subgroup.normalizer_eq_top_iff.mp hN_top)
      obtain ⟨M, hM_coatom, hN_le_M⟩ :=
        (eq_top_or_exists_le_coatom (Subgroup.normalizer (S : Set G))).resolve_left hN_lt_top.ne
      have hS_le_NS : S ≤ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer
      have hS_le_M : S ≤ M := hS_le_NS.trans hN_le_M
      refine ⟨M, hM_coatom, hS_le_M, ?_⟩
      intro K hK_coatom hS_le_K
      have hK_ne_top : K ≠ ⊤ := hK_coatom.1
      have hSsubK_sn : (S.subgroupOf K).IsSubnormal := hS_proper K hS_le_K hK_ne_top
      by_cases hSK_normal : (S.subgroupOf K).Normal
      · have hK_le_NS : K ≤ Subgroup.normalizer (S : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_K).mp hSK_normal
        have hK_le_M : K ≤ M := hK_le_NS.trans hN_le_M
        rcases hK_coatom.le_iff.mp hK_le_M with hM_top | hM_eq
        · exact absurd hM_top hM_coatom.1
        · exact hM_eq.symm
      · obtain ⟨nChain, f, hf_mono, hf_step, hf0, hfN⟩ :=
          hSsubK_sn.exists_chain
        have hPred_exists : ∃ i, ¬ (((S.subgroupOf K).subgroupOf (f i)).Normal) := by
          refine ⟨nChain, ?_⟩
          intro hN
          apply hSK_normal
          rw [hfN] at hN
          have h1 : (⊤ : Subgroup K) ≤
              Subgroup.normalizer ((S.subgroupOf K) : Set K) :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hN
          rw [top_le_iff, Subgroup.normalizer_eq_top_iff] at h1
          exact h1
        let m := Nat.find hPred_exists
        have hm_spec : ¬ (((S.subgroupOf K).subgroupOf (f m)).Normal) := Nat.find_spec hPred_exists
        have hm_min : ∀ k < m, ((S.subgroupOf K).subgroupOf (f k)).Normal := by
          intro k hk
          by_contra h
          exact absurd (Nat.find_min hPred_exists hk) (not_not.mpr h)
        have hm_pos : 0 < m := by
          by_contra h
          push Not at h
          interval_cases m
          apply hm_spec
          rw [hf0]
          rw [show (S.subgroupOf K).subgroupOf (S.subgroupOf K) = ⊤ from
            Subgroup.subgroupOf_self _]
          exact Subgroup.normal_top
        have hfm1_norm : ((S.subgroupOf K).subgroupOf (f (m - 1))).Normal :=
          hm_min (m - 1) (Nat.sub_lt hm_pos Nat.zero_lt_one)
        have hS_le_fm1 : S.subgroupOf K ≤ f (m - 1) := by
          rw [← hf0]; exact hf_mono (Nat.zero_le _)
        have hfm1_le_norm : f (m - 1) ≤
            Subgroup.normalizer ((S.subgroupOf K) : Set K) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_fm1).mp hfm1_norm
        have hS_le_fm : S.subgroupOf K ≤ f m := by
          rw [← hf0]; exact hf_mono (Nat.zero_le _)
        have hfm_not_le_norm : ¬ (f m ≤
            Subgroup.normalizer ((S.subgroupOf K) : Set K)) := by
          intro h
          exact hm_spec ((Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_fm).mpr h)
        obtain ⟨x, hx_in_fm, hx_not_norm⟩ : ∃ x : K, x ∈ f m ∧
            x ∉ Subgroup.normalizer ((S.subgroupOf K) : Set K) := by
          by_contra h
          push Not at h
          apply hfm_not_le_norm
          intro y hy
          exact h y hy
        have hfm1_le_fm : f (m - 1) ≤ f m := by
          have : m - 1 ≤ m := Nat.sub_le _ _
          exact hf_mono this
        have hfm1_norm_in_fm : ((f (m - 1)).subgroupOf (f m)).Normal := by
          have hstep := hf_step (m - 1)
          rwa [Nat.sub_add_cancel hm_pos] at hstep
        have hfm_le_normfm1 : f m ≤ Subgroup.normalizer ((f (m - 1)) : Set K) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hfm1_le_fm).mp hfm1_norm_in_fm
        set xG : G := (x : G)
        have hxG_in_K : xG ∈ K := x.2
        let J : Subgroup G := (f (m - 1)).map K.subtype
        have hS_le_J : S ≤ J := by
          rw [show S = (S.subgroupOf K).map K.subtype from
            (Subgroup.map_subgroupOf_eq_of_le hS_le_K).symm]
          exact Subgroup.map_mono hS_le_fm1
        have hJ_le_K : J ≤ K := by
          rintro _ ⟨⟨y, hyK⟩, _, rfl⟩
          exact hyK
        have hJ_le_NS : J ≤ Subgroup.normalizer (S : Set G) := by
          intro y hy
          rcases hy with ⟨⟨y', hy'K⟩, hy'_in, rfl⟩
          have hy'_norm : (⟨y', hy'K⟩ : K) ∈
              Subgroup.normalizer ((S.subgroupOf K) : Set K) := hfm1_le_norm hy'_in
          rw [Subgroup.mem_normalizer_iff] at hy'_norm ⊢
          intro s
          by_cases hsK : s ∈ K
          · have h := hy'_norm ⟨s, hsK⟩
            constructor
            · intro hsS
              have h1 : (⟨s, hsK⟩ : K) ∈ S.subgroupOf K := by
                rwa [Subgroup.mem_subgroupOf]
              have h2 := h.mp h1
              rw [Subgroup.mem_subgroupOf] at h2
              exact h2
            · intro hys
              have hys_in_K : y' * s * y'⁻¹ ∈ K :=
                K.mul_mem (K.mul_mem hy'K hsK) (K.inv_mem hy'K)
              have h1 : (⟨y' * s * y'⁻¹, hys_in_K⟩ : K) ∈ S.subgroupOf K := by
                rwa [Subgroup.mem_subgroupOf]
              have hcong : (⟨y' * s * y'⁻¹, hys_in_K⟩ : K) =
                  ⟨y', hy'K⟩ * ⟨s, hsK⟩ * ⟨y', hy'K⟩⁻¹ := by
                apply Subtype.ext
                change y' * s * y'⁻¹ =
                  ((⟨y', hy'K⟩ * ⟨s, hsK⟩ * ⟨y', hy'K⟩⁻¹ : K) : G)
                push_cast
                rfl
              rw [hcong] at h1
              have h2 := h.mpr h1
              rwa [Subgroup.mem_subgroupOf] at h2
          · have hys_notK : y' * s * y'⁻¹ ∉ K := by
              intro h
              apply hsK
              have hseq : s = y'⁻¹ * (y' * s * y'⁻¹) * y' := by group
              rw [hseq]
              exact K.mul_mem (K.mul_mem (K.inv_mem hy'K) h) hy'K
            constructor
            · intro hsS; exact absurd (hS_le_K hsS) hsK
            · intro hys; exact absurd (hS_le_K hys) hys_notK
        set Sx : Subgroup G := (MulAut.conj xG⁻¹ : MulAut G) • S with hSx_def
        set T : Subgroup G := S ⊔ Sx with hT_def
        have hJ_normalizes_xG : (MulAut.conj xG : MulAut G) • J ≤ J := by
          rintro - ⟨z, hzJ, rfl⟩
          rcases hzJ with ⟨⟨z', hz'K⟩, hz'_in_fm1, rfl⟩
          have hx_norm_fm1 : x ∈ Subgroup.normalizer ((f (m - 1)) : Set K) :=
            hfm_le_normfm1 hx_in_fm
          have h_conj : x * ⟨z', hz'K⟩ * x⁻¹ ∈ f (m - 1) :=
            ((Subgroup.mem_normalizer_iff.mp hx_norm_fm1) ⟨z', hz'K⟩).mp hz'_in_fm1
          refine ⟨x * ⟨z', hz'K⟩ * x⁻¹, h_conj, ?_⟩
          change ((x * ⟨z', hz'K⟩ * x⁻¹ : K) : G) = MulAut.conj xG z'
          push_cast
          simp [xG]
        have hx_inv_in_fm : x⁻¹ ∈ f m := (f m).inv_mem hx_in_fm
        have hJ_normalizes_xG_inv : (MulAut.conj xG⁻¹ : MulAut G) • J ≤ J := by
          rintro - ⟨z, hzJ, rfl⟩
          rcases hzJ with ⟨⟨z', hz'K⟩, hz'_in_fm1, rfl⟩
          have hxinv_norm_fm1 : x⁻¹ ∈ Subgroup.normalizer ((f (m - 1)) : Set K) :=
            hfm_le_normfm1 hx_inv_in_fm
          have h_conj : x⁻¹ * ⟨z', hz'K⟩ * x⁻¹⁻¹ ∈ f (m - 1) :=
            ((Subgroup.mem_normalizer_iff.mp hxinv_norm_fm1) ⟨z', hz'K⟩).mp hz'_in_fm1
          refine ⟨x⁻¹ * ⟨z', hz'K⟩ * x⁻¹⁻¹, h_conj, ?_⟩
          change ((x⁻¹ * ⟨z', hz'K⟩ * x⁻¹⁻¹ : K) : G) = MulAut.conj xG⁻¹ z'
          push_cast
          simp [xG]
        have hSx_le_J : Sx ≤ J := by
          rw [hSx_def]
          calc (MulAut.conj xG⁻¹ : MulAut G) • S
              ≤ (MulAut.conj xG⁻¹ : MulAut G) • J :=
                Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hS_le_J
            _ ≤ J := hJ_normalizes_xG_inv
        have hSx_le_NS : Sx ≤ Subgroup.normalizer (S : Set G) := hSx_le_J.trans hJ_le_NS
        have hSx_le_K : Sx ≤ K := hSx_le_J.trans hJ_le_K
        have hT_le_NS : T ≤ Subgroup.normalizer (S : Set G) :=
          sup_le hS_le_NS hSx_le_NS
        have hT_le_K : T ≤ K := sup_le hS_le_K hSx_le_K
        have hT_le_M : T ≤ M := hT_le_NS.trans hN_le_M
        have hSx_card : Nat.card Sx = Nat.card S :=
          Nat.card_congr (Subgroup.equivSMul (MulAut.conj xG⁻¹) S).toEquiv.symm
        have hSx_not_le_S : ¬ (Sx ≤ S) := by
          intro h
          have hSx_eq : Sx = S := Subgroup.eq_of_le_of_card_ge h hSx_card.ge
          have hxG_norm_S : xG ∈ Subgroup.normalizer (S : Set G) := by
            rw [Subgroup.mem_normalizer_iff]
            intro u
            constructor
            · intro huS
              have hsmul_eq : (MulAut.conj xG : MulAut G) • S = S := by
                have h1 : (MulAut.conj xG⁻¹ : MulAut G) • S = S := hSx_eq
                have h2 : (MulAut.conj xG : MulAut G)⁻¹ • S = S := by
                  rw [← map_inv MulAut.conj]; exact h1
                calc (MulAut.conj xG : MulAut G) • S
                    = (MulAut.conj xG : MulAut G) •
                      ((MulAut.conj xG : MulAut G)⁻¹ • S) := by rw [h2]
                  _ = S := by rw [smul_inv_smul]
              have hu_smul : MulAut.conj xG u ∈ (MulAut.conj xG : MulAut G) • S := ⟨u, huS, rfl⟩
              rw [hsmul_eq] at hu_smul
              change xG * u * xG⁻¹ ∈ S
              exact hu_smul
            · intro hxu
              have h_smul_eq : (MulAut.conj xG⁻¹ : MulAut G) • S = S := hSx_eq
              have : MulAut.conj xG⁻¹ (xG * u * xG⁻¹) ∈ (MulAut.conj xG⁻¹ : MulAut G) • S :=
                ⟨xG * u * xG⁻¹, hxu, rfl⟩
              rw [h_smul_eq] at this
              have hsimp : MulAut.conj xG⁻¹ (xG * u * xG⁻¹) = u := by
                change xG⁻¹ * (xG * u * xG⁻¹) * (xG⁻¹)⁻¹ = u
                group
              rwa [hsimp] at this
          apply hx_not_norm
          rw [Subgroup.mem_normalizer_iff]
          intro a
          have hmem : ∀ b : K, b ∈ S.subgroupOf K ↔ (b : G) ∈ S := fun b => Subgroup.mem_subgroupOf
          rw [hmem a]
          have hcoe : (((x : K) * a * (x : K)⁻¹ : K) : G) = xG * (a : G) * xG⁻¹ := by
            push_cast; rfl
          rw [hmem _, hcoe]
          rw [Subgroup.mem_normalizer_iff] at hxG_norm_S
          exact hxG_norm_S a
        have hS_le_T : S ≤ T := le_sup_left
        have hS_lt_T : S < T := by
          refine lt_of_le_of_ne hS_le_T ?_
          intro hST
          apply hSx_not_le_S
          have : Sx ≤ T := le_sup_right
          rw [← hST] at this
          exact this
        haveI : S.FiniteIndex := ⟨by rw [hIdx]; omega⟩
        have hT_idx_lt : T.index < S.index := Subgroup.index_strictAnti hS_lt_T
        have hT_not_sn : ¬ T.IsSubnormal := by
          intro hT_sn
          apply hS_not_sn
          have hS_norm_T : (S.subgroupOf T).Normal :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_T).mpr hT_le_NS
          exact Subgroup.IsSubnormal.trans hS_le_T hS_norm_T.isSubnormal hT_sn
        have hT_proper : ∀ H : Subgroup G, T ≤ H → H ≠ ⊤ → (T.subgroupOf H).IsSubnormal := by
          intro H hTH hH_ne
          have hS_le_H : S ≤ H := hS_le_T.trans hTH
          have hSx_le_H : Sx ≤ H := le_sup_right.trans hTH
          have h1 : (S.subgroupOf H).IsSubnormal := hS_proper H hS_le_H hH_ne
          have hH_conj_ne_top : (MulAut.conj xG : MulAut G) • H ≠ ⊤ := by
            intro h
            apply hH_ne
            have h1 : (MulAut.conj xG : MulAut G) • H = (MulAut.conj xG : MulAut G) • ⊤ := by
              rw [h]
              ext y
              simp
            have h2 : H ≤ ⊤ := le_top
            have h3 : ⊤ ≤ H :=
              Subgroup.pointwise_smul_le_pointwise_smul_iff.mp h1.ge
            exact le_antisymm h2 h3
          have hS_le_HConj : S ≤ (MulAut.conj xG : MulAut G) • H := by
            have hSx_eq : (MulAut.conj xG : MulAut G) • Sx = S := by
              rw [hSx_def, ← smul_assoc]
              change (MulAut.conj xG * MulAut.conj xG⁻¹ : MulAut G) • S = S
              rw [← map_mul, mul_inv_cancel, map_one]
              exact one_smul _ _
            rw [← hSx_eq]
            exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hSx_le_H
          have h_sub_subn : (S.subgroupOf ((MulAut.conj xG : MulAut G) • H)).IsSubnormal :=
            hS_proper _ hS_le_HConj hH_conj_ne_top
          let φ : H →* ((MulAut.conj xG : MulAut G) • H : Subgroup G) :=
            (Subgroup.equivSMul (MulAut.conj xG) H).toMonoidHom
          have hφ_surj : Function.Surjective φ :=
            (Subgroup.equivSMul (MulAut.conj xG) H).surjective
          have hcomap_eq : (S.subgroupOf ((MulAut.conj xG : MulAut G) • H)).comap φ =
              Sx.subgroupOf H := by
            ext ⟨h, hhH⟩
            constructor
            · intro hh
              rw [Subgroup.mem_subgroupOf]
              rw [Subgroup.mem_comap] at hh
              rw [Subgroup.mem_subgroupOf] at hh
              refine ⟨xG * h * xG⁻¹, hh, ?_⟩
              change xG⁻¹ * (xG * h * xG⁻¹) * (xG⁻¹)⁻¹ = h
              group
            · intro hh
              rw [Subgroup.mem_comap]
              rw [Subgroup.mem_subgroupOf] at hh
              rw [Subgroup.mem_subgroupOf]
              rcases hh with ⟨s, hsS, hhs⟩
              have hφ_coe : (((φ ⟨h, hhH⟩) :
                  ((MulAut.conj xG : MulAut G) • H : Subgroup G)) : G) = xG * h * xG⁻¹ := rfl
              have hsh : xG * h * xG⁻¹ = s := by
                have hh_eq : xG⁻¹ * s * xG = h := by
                  have hh_eq' : (MulAut.conj xG⁻¹ : MulAut G) s = h := hhs
                  have h2 : (MulAut.conj xG⁻¹ : MulAut G) s = xG⁻¹ * s * xG := by
                    change xG⁻¹ * s * (xG⁻¹)⁻¹ = xG⁻¹ * s * xG
                    rw [inv_inv]
                  rw [← h2]; exact hh_eq'
                have : s = xG * h * xG⁻¹ := by rw [← hh_eq]; group
                exact this.symm
              rw [hφ_coe, hsh]; exact hsS
          have h2 : (Sx.subgroupOf H).IsSubnormal := hcomap_eq ▸ h_sub_subn.comap φ
          have hsup : ((S.subgroupOf H) ⊔ (Sx.subgroupOf H)).IsSubnormal :=
            isSubnormal_sup_of_isSubnormal h1 h2
          rw [show (S.subgroupOf H) ⊔ (Sx.subgroupOf H) = T.subgroupOf H from
            (Subgroup.subgroupOf_sup hS_le_H hSx_le_H).symm] at hsup
          exact hsup
        obtain ⟨M', hM'_coatom, _, hM'_uniq⟩ :=
          ih T.index (hIdx ▸ hT_idx_lt) hT_proper hT_not_sn rfl
        have hM_eq_M' : M = M' := hM'_uniq M hM_coatom hT_le_M
        have hK_eq_M' : K = M' := hM'_uniq K hK_coatom hT_le_K
        rw [hM_eq_M', hK_eq_M']

/-! ### Isaacs Thm 2.12 (Baer): `H ≤ F(G) ↔ ∀ x, ⟨H, H^x⟩` nilpotent -/

/-- **Isaacs Thm 2.12**, easy direction: `H ≤ F(G)` implies `⟨H, H^x⟩` nilpotent. -/
theorem baer_sup_conj_isNilpotent_of_le_fitting [Finite G] {H : Subgroup G}
    (hH : H ≤ fitting G) (x : G) :
    Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G)) := by
  have hFnormal : (MulAut.conj x : MulAut G) • (fitting G : Subgroup G) = fitting G :=
    Subgroup.Normal.conj_smul_eq_self (h := fitting.normal G) x (fitting G)
  have hHx_le : ((MulAut.conj x) • H : Subgroup G) ≤ fitting G := by
    rw [← hFnormal]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hH
  have hSup_le : (H ⊔ ((MulAut.conj x) • H : Subgroup G)) ≤ fitting G := sup_le hH hHx_le
  exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSup_le)

private theorem le_fitting_of_baer_aux :
    ∀ n, ∀ (G : Type*) [Group G] [Finite G],
      Nat.card G ≤ n → ∀ {H : Subgroup G},
      (∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G))) →
      H ≤ fitting G := by
  intro n
  induction n with
  | zero =>
    intro G _ _ hG _ _
    exact absurd (Nat.le_zero.mp hG) Nat.card_pos.ne'
  | succ n ih =>
    intro G _ _ _ H hN
    have hH_nilp : Group.IsNilpotent ↥H := by
      have h1 := hN 1
      rw [map_one, one_smul, sup_idem] at h1
      exact h1
    suffices hSn : H.IsSubnormal from
      (le_fitting_iff_isNilpotent_and_isSubnormal H).mpr ⟨hH_nilp, hSn⟩
    by_contra hSnneg
    have hIH : ∀ K : Subgroup G, H ≤ K → K ≠ ⊤ →
        (H.subgroupOf K).IsSubnormal := by
      intro K hHK hKne
      have hK_card : Nat.card K ≤ n := by
        have hKle : Nat.card K ≤ Nat.card G := K.card_le_card_group
        have hKne_card : Nat.card K ≠ Nat.card G := fun heq =>
          hKne (Subgroup.eq_top_of_card_eq K heq)
        omega
      have hIH_K : (H.subgroupOf K) ≤ fitting K := by
        apply ih K hK_card
        intro y
        rw [Subgroup.conj_smul_subgroupOf hHK]
        have hHy_le_K : ((MulAut.conj (y : G)) • H : Subgroup G) ≤ K :=
          Subgroup.conj_smul_le_of_le hHK y
        rw [← Subgroup.subgroupOf_sup hHK hHy_le_K]
        haveI : Group.IsNilpotent
            ↥(H ⊔ ((MulAut.conj (y : G)) • H) : Subgroup G) := hN (y : G)
        have hsup_le_K : (H ⊔ ((MulAut.conj (y : G)) • H) : Subgroup G) ≤ K :=
          sup_le hHK hHy_le_K
        exact nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hsup_le_K).symm
      exact ((le_fitting_iff_isNilpotent_and_isSubnormal _).mp hIH_K).2
    obtain ⟨M, hMcoatom, _, hMuniq⟩ := zipper_lemma hIH hSnneg
    have hHx_le_M : ∀ x : G, ((MulAut.conj x) • H : Subgroup G) ≤ M := by
      intro x
      have hNx := hN x
      have hsup_ne_top : (H ⊔ ((MulAut.conj x) • H : Subgroup G)) ≠ ⊤ := by
        intro h_top
        apply hSnneg
        rw [h_top] at hNx
        haveI := hNx
        haveI hG_nilp : Group.IsNilpotent G :=
          nilpotent_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
        exact isSubnormal_of_isNilpotent_finite H
      obtain ⟨K, hKcoatom, hKle⟩ :=
        (eq_top_or_exists_le_coatom (H ⊔ ((MulAut.conj x) • H : Subgroup G) :
          Subgroup G)).resolve_left hsup_ne_top
      have hHK : H ≤ K := le_sup_left.trans hKle
      have hKM : K = M := hMuniq K hKcoatom hHK
      exact (le_sup_right.trans hKle).trans hKM.le
    have hNH_le_M : Subgroup.normalClosure (H : Set G) ≤ M := by
      rw [Subgroup.normalClosure, Subgroup.closure_le]
      intro y hy
      rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨a, haH, hConj⟩
      rcases hConj with ⟨c, hc⟩
      apply hHx_le_M (c : G)
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def]
      change ((c : G)⁻¹) * y * ((c : G)⁻¹)⁻¹ ∈ H
      rw [inv_inv]
      have hc_eq : (c : G) * a = y * (c : G) := hc
      have ha_eq : ((c : G)⁻¹) * y * ((c : G)) = a := by
        rw [mul_assoc, ← hc_eq]
        group
      rw [ha_eq]
      exact haH
    have hNH_lt : Subgroup.normalClosure (H : Set G) ≠ ⊤ := fun hNHtop =>
      hMcoatom.1 (le_top.antisymm (hNHtop.symm.le.trans hNH_le_M))
    have hHle_NH : H ≤ Subgroup.normalClosure (H : Set G) :=
      Subgroup.le_normalClosure
    have hH_sn_in_NH : (H.subgroupOf (Subgroup.normalClosure (H : Set G))).IsSubnormal :=
      hIH _ hHle_NH hNH_lt
    have hNH_sn : (Subgroup.normalClosure (H : Set G)).IsSubnormal :=
      Subgroup.Normal.isSubnormal inferInstance
    exact hSnneg (Subgroup.IsSubnormal.trans hHle_NH hH_sn_in_NH hNH_sn)

/-- **Isaacs Thm 2.12**, hard direction: `∀ x, ⟨H, H^x⟩` nilpotent implies `H ≤ F(G)`. -/
theorem le_fitting_of_baer_sup_conj_isNilpotent [Finite G] {H : Subgroup G}
    (hN : ∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G))) :
    H ≤ fitting G :=
  le_fitting_of_baer_aux (Nat.card G) G le_rfl hN

/-- **Isaacs Thm 2.12 (Baer's theorem)**. `H ≤ F(G) ↔ ∀ x, ⟨H, H^x⟩` is nilpotent. -/
theorem le_fitting_iff_baer_sup_conj_isNilpotent [Finite G] (H : Subgroup G) :
    H ≤ fitting G ↔
      ∀ x : G, Group.IsNilpotent ↥(H ⊔ ((MulAut.conj x) • H : Subgroup G)) :=
  ⟨fun hH => baer_sup_conj_isNilpotent_of_le_fitting hH,
   le_fitting_of_baer_sup_conj_isNilpotent⟩

/-! ### Bridge: `H ≤ F(G)` + `p`-group ⇒ `H ≤ O_p(G)` -/

/-- If `H ≤ F(G)` is a `p`-subgroup then `H ≤ O_p(G)`. The Fitting subgroup is
nilpotent, so its Sylow `p`-subgroup is unique and normal, hence characteristic
in `F(G)`; lifting to `G` and applying `normal_pgroup_le_opCore` gives the
inclusion. -/
theorem mem_opCore_of_le_fitting_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hH_pgroup : IsPGroup p H) (hH_fit : H ≤ fitting G) :
    H ≤ opCore p G := by
  set Hin : Subgroup (fitting G) := H.subgroupOf (fitting G) with hHin_def
  have hHin_pgroup : IsPGroup p Hin :=
    hH_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hH_fit).symm
  obtain ⟨Q, hHin_le_Q⟩ := hHin_pgroup.exists_le_sylow
  haveI hQ_normal : (Q : Subgroup (fitting G)).Normal := Sylow.normal_of_isNilpotent _
  haveI hQ_char : (Q : Subgroup (fitting G)).Characteristic :=
    Sylow.characteristic_of_normal _ hQ_normal
  haveI : ((Q : Subgroup (fitting G)).map (fitting G).subtype).Normal := inferInstance
  have hpgroupG : IsPGroup p ((Q : Subgroup (fitting G)).map (fitting G).subtype) :=
    Q.2.map (fitting G).subtype
  have hQ_le_op : (Q : Subgroup (fitting G)).map (fitting G).subtype ≤ opCore p G :=
    normal_pgroup_le_opCore hpgroupG
  intro x hx
  have hx_fit : x ∈ fitting G := hH_fit hx
  have hx_Hin : (⟨x, hx_fit⟩ : fitting G) ∈ Hin := by
    rw [hHin_def, Subgroup.mem_subgroupOf]
    exact hx
  have hx_Q : (⟨x, hx_fit⟩ : fitting G) ∈ (Q : Subgroup (fitting G)) :=
    hHin_le_Q hx_Hin
  exact hQ_le_op ⟨⟨x, hx_fit⟩, hx_Q, rfl⟩

/-! ### Single-element Baer-Suzuki theorem -/

/-- **Baer-Suzuki theorem (single-element p-core form)**. For a finite group
`G`, prime `p`, and element `x : G`,

  `x ∈ O_p(G) ↔ ∀ g : G, ⟨x, g·x·g⁻¹⟩ is a p-group`.

The forward direction is immediate (`O_p(G)` is normal and a `p`-group, so it
contains every closure as a `p`-group). The reverse direction specialises
Isaacs Thm 2.12 (Baer) to `H = ⟨x⟩` and then bridges `F(G) → O_p(G)`.
-/
theorem baerSuzukiP [Finite G] {p : ℕ} [Fact p.Prime] (x : G) :
    x ∈ opCore p G ↔
      ∀ g : G, IsPGroup p ↥(Subgroup.closure ({x, g * x * g⁻¹} : Set G)) := by
  refine ⟨?_, ?_⟩
  · intro hx g
    have hOp_pgroup : IsPGroup p ↥(opCore p G) := opCore_isPGroup p G
    have hgx : g * x * g⁻¹ ∈ opCore p G :=
      (opCore.normal p G).conj_mem x hx g
    have hclos_le : Subgroup.closure ({x, g * x * g⁻¹} : Set G) ≤ opCore p G := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with rfl | hy
      · exact hx
      · rw [Set.mem_singleton_iff] at hy
        exact hy ▸ hgx
    exact hOp_pgroup.of_injective (Subgroup.inclusion hclos_le)
      (Subgroup.inclusion_injective hclos_le)
  · intro hPg
    have hx_pgroup : IsPGroup p ↥(Subgroup.zpowers x) := by
      have h1 := hPg 1
      have h_set : ({x, 1 * x * 1⁻¹} : Set G) = {x} := by simp
      rw [h_set, ← Subgroup.zpowers_eq_closure] at h1
      exact h1
    have hsup_eq : ∀ g : G,
        (Subgroup.zpowers x ⊔ ((MulAut.conj g) • Subgroup.zpowers x : Subgroup G))
          = Subgroup.closure ({x, g * x * g⁻¹} : Set G) := by
      intro g
      have h_conj : (MulAut.conj g : MulAut G) • Subgroup.zpowers x
          = Subgroup.zpowers (g * x * g⁻¹) := by
        rw [Subgroup.zpowers_eq_closure x,
            Subgroup.zpowers_eq_closure (g * x * g⁻¹),
            Subgroup.smul_closure]
        congr 1
        ext y
        simp [MulAut.smul_def, MulAut.conj_apply]
      rw [h_conj, Subgroup.zpowers_eq_closure x,
          Subgroup.zpowers_eq_closure (g * x * g⁻¹),
          ← Subgroup.closure_union]
      congr 1
    have hbaer : ∀ g : G,
        Group.IsNilpotent ↥(Subgroup.zpowers x ⊔
          ((MulAut.conj g) • Subgroup.zpowers x : Subgroup G)) := by
      intro g
      rw [hsup_eq g]
      exact (hPg g).isNilpotent
    have hxle_fit : Subgroup.zpowers x ≤ fitting G :=
      (le_fitting_iff_baer_sup_conj_isNilpotent _).mpr hbaer
    exact mem_opCore_of_le_fitting_of_isPGroup hx_pgroup hxle_fit
      (Subgroup.mem_zpowers x)

end Submission.Helpers
