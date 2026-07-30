import Submission.OddOrder.PF.Section05.KernelCounting

/-!
# Global families of induced irreducible characters

This file ports `PFsection5.v`, lines 265--441.  It packages the full family
of characters induced from a normal subgroup, the layers selected by two
kernel bounds, their coefficient-automorphism and contragredient closure,
the odd-order orthogonality consequences, and the degree-square identity.

The Coq source uses duplicate-free sequences.  Here all such families are
`Finset`s.  If `K ◁ G`, the two kernel bounds in `seqIndD K H M` are
subgroups of `K`; the family consists of the inductions of the irreducible
characters of `K` whose translation kernel contains `M` but not `H`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u v

local instance seqIndGlobalInvertibleCard
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [CharZero k] : Invertible (Nat.card G : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## The full induced family and kernel layers -/

/-- Source `seqIndS`: induction is monotone in the finite family of
inducing irreducibles. -/
theorem seqIndS {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G)
    {calX calY : Finset (IrreducibleCharacter K k)}
    (hXY : calX ⊆ calY) :
    seqInd K calX ⊆ seqInd K calY := by
  intro phi hphi
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  exact seqIndP.mpr ⟨chi, hXY hchi, rfl⟩

/-- Source `seqIndT`: all class functions induced from irreducible
characters of `K`. -/
def seqIndT {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) : Finset (ClassFunction G k) :=
  seqInd K Finset.univ

/-- Every selected induced family is contained in the full one. -/
theorem seqInd_subT {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (calX : Finset (IrreducibleCharacter K k)) :
    seqInd K calX ⊆ seqIndT K :=
  seqIndS K (fun _ _ ↦ Finset.mem_univ _)

/-- Every induced irreducible belongs to `seqIndT`. -/
theorem mem_seqIndT {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (chi : IrreducibleCharacter K k) :
    ClassFunction.induce K (chi : ClassFunction K k) ∈ seqIndT K :=
  seqIndP.mpr ⟨chi, Finset.mem_univ _, rfl⟩

/-- The character induced from the trivial character belongs to the full
induced family. -/
theorem seqIndT_Ind1 {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) :
    ClassFunction.induce K
        ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
          ClassFunction K k) ∈ seqIndT K :=
  mem_seqIndT K IrreducibleCharacter.trivial

/-- Source `seqIndD`: the induced family between two kernel bounds. -/
def seqIndD {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (H M : Subgroup K) :
    Finset (ClassFunction G k) :=
  seqInd K (Iirr_kerD (k := k) H M)

/-- Source `seqIndDY`: adjoining the lower kernel bound to the excluded
upper bound does not change the layer. -/
theorem seqIndDY {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (H M : Subgroup K) :
    seqIndD (k := k) K (M ⊔ H) M = seqIndD (k := k) K H M := by
  unfold seqIndD
  rw [Iirr_kerDY (k := k) H M]

/-! ## Coefficient automorphisms -/

/-- Pointwise coefficient automorphisms commute with induction. -/
theorem ClassFunction.mapRingHom_induce
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [CharZero k]
    (sigma : k ≃+* k) (K : Subgroup G) (f : ClassFunction K k) :
    ClassFunction.mapRingHom sigma.toRingHom (ClassFunction.induce K f) =
      ClassFunction.induce K
        (ClassFunction.mapRingHom sigma.toRingHom f) := by
  classical
  ext g
  rw [ClassFunction.mapRingHom_apply,
    ClassFunction.induce_apply_formula,
    ClassFunction.induce_apply_formula]
  rw [map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x⁻¹ * g * x ∈ K
  · rw [dif_pos hx, dif_pos hx, ClassFunction.mapRingHom_apply]
  · rw [dif_neg hx, dif_neg hx, map_zero]

/-- Coercing a coefficient-twisted irreducible character gives pointwise
application of the coefficient automorphism. -/
@[simp]
theorem ClassFunction.mapRingHom_irreducible
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (sigma : k ≃+* k) (chi : IrreducibleCharacter G k) :
    ClassFunction.mapRingHom sigma.toRingHom
        (chi : ClassFunction G k) =
      (IrreducibleCharacter.mapRingEquiv sigma chi : ClassFunction G k) := by
  ext g
  simp

/-- Source `cfAut_seqIndT`: coefficient automorphisms permute the full
induced family. -/
theorem cfAut_seqIndT {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (sigma : k ≃+* k) (K : Subgroup G)
    {phi : ClassFunction G k} (hphi : phi ∈ seqIndT K) :
    ClassFunction.mapRingHom sigma.toRingHom phi ∈ seqIndT K := by
  obtain ⟨chi, _, rfl⟩ := seqIndP.mp hphi
  apply seqIndP.mpr
  refine ⟨IrreducibleCharacter.mapRingEquiv sigma chi,
    Finset.mem_univ _, ?_⟩
  rw [ClassFunction.mapRingHom_induce,
    ClassFunction.mapRingHom_irreducible]

/-- Source `cfAut_seqInd`: coefficient automorphisms preserve every kernel
layer. -/
theorem cfAut_seqInd {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (sigma : k ≃+* k) (K : Subgroup G) (H M : Subgroup K)
    {phi : ClassFunction G k} (hphi : phi ∈ seqIndD (k := k) K H M) :
    ClassFunction.mapRingHom sigma.toRingHom phi ∈ seqIndD (k := k) K H M := by
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  apply seqIndP.mpr
  refine ⟨IrreducibleCharacter.mapRingEquiv sigma chi, ?_, ?_⟩
  · rw [mem_Iirr_kerD (k := k)] at hchi ⊢
    simpa only [translationKernel_mapRingEquiv] using hchi
  · rw [ClassFunction.mapRingHom_induce,
      ClassFunction.mapRingHom_irreducible]

/-! ## The nontrivial layer -/

/-- Source `mem_seqInd`: when the kernel bounds are stable under ambient
conjugation, membership of an induced irreducible in the layer is exactly
membership of its inducing character. -/
theorem mem_seqInd {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (H M : Subgroup K)
    [((H.map K.subtype : Subgroup G)).Normal]
    [((M.map K.subtype : Subgroup G)).Normal]
    (chi : IrreducibleCharacter K k) :
    ClassFunction.induce K (chi : ClassFunction K k) ∈
        seqIndD (k := k) K H M ↔
      chi ∈ Iirr_kerD (k := k) H M := by
  constructor
  · intro hind
    obtain ⟨xi, hxi, heq⟩ := seqIndP.mp hind
    have horbit : chi ∈ MulAction.orbit G xi :=
      (ClassFunction.cfclass_Ind_irrP K chi xi).2 heq
    rw [MulAction.mem_orbit_iff] at horbit
    obtain ⟨x, hx⟩ := horbit
    rw [← hx]
    rw [mem_Iirr_kerD (k := k)] at hxi ⊢
    have hHK : H.map K.subtype ≤ K := by
      rintro y ⟨h, hh, rfl⟩
      exact h.property
    have hMK : M.map K.subtype ≤ K := by
      rintro y ⟨m, hm, rfl⟩
      exact m.property
    have hHsub : (H.map K.subtype).subgroupOf K = H := by
      change (H.map K.subtype).comap K.subtype = H
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective H
    have hMsub : (M.map K.subtype).subgroupOf K = M := by
      change (M.map K.subtype).comap K.subtype = M
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective M
    have hxH : x ∈ Subgroup.normalizer (H.map K.subtype : Set G) := by
      rw [Subgroup.normalizer_eq_top]
      trivial
    have hxM : x ∈ Subgroup.normalizer (M.map K.subtype : Set G) := by
      rw [Subgroup.normalizer_eq_top]
      trivial
    constructor
    · rw [← hMsub]
      apply (mem_Iirr_ker (k := k)).mp
      apply
        (Iirr_ker_conjg (k := k) K (M.map K.subtype)
          hMK x hxM xi).mpr
      apply (mem_Iirr_ker (k := k)).mpr
      simpa only [hMsub] using hxi.1
    · intro hH
      apply hxi.2
      rw [← hHsub]
      apply (mem_Iirr_ker (k := k)).mp
      apply
        (Iirr_ker_conjg (k := k) K (H.map K.subtype)
          hHK x hxH xi).mp
      apply (mem_Iirr_ker (k := k)).mpr
      rwa [hHsub]
  · intro hchi
    exact seqIndP.mpr ⟨chi, hchi, rfl⟩

/-- Source `seqIndC1P`: the layer between `⊥` and `⊤` consists of the
inductions of nontrivial irreducible characters. -/
theorem seqIndC1P {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) {phi : ClassFunction G k} :
    phi ∈ seqIndD (k := k) K ⊤ ⊥ ↔
      ∃ chi : IrreducibleCharacter K k,
        chi ≠ IrreducibleCharacter.trivial ∧
        phi = ClassFunction.induce K (chi : ClassFunction K k) := by
  rw [seqIndD, seqIndP]
  constructor
  · rintro ⟨chi, hchi, rfl⟩
    exact ⟨chi, (mem_Iirr_ker1 chi).mp hchi, rfl⟩
  · rintro ⟨chi, hchi, rfl⟩
    exact ⟨chi, (mem_Iirr_ker1 chi).mpr hchi, rfl⟩

/-- The nontrivial layer is obtained by filtering the induced trivial
character out of the full family. -/
theorem seqIndC1_filter {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal] :
    seqIndD (k := k) K ⊤ ⊥ =
      (seqIndT K).filter fun phi ↦
        phi ≠ ClassFunction.induce K
          ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
            ClassFunction K k) := by
  ext phi
  simp only [Finset.mem_filter]
  constructor
  · intro hphi
    obtain ⟨chi, hchi, rfl⟩ := (seqIndC1P (k := k) K).mp hphi
    refine ⟨mem_seqIndT K chi, ?_⟩
    intro heq
    have horbit :=
      (ClassFunction.cfclass_Ind_irrP K chi
        (IrreducibleCharacter.trivial : IrreducibleCharacter K k)).2 heq
    rw [MulAction.mem_orbit_iff] at horbit
    obtain ⟨x, hx⟩ := horbit
    apply hchi
    calc
      chi =
          IrreducibleCharacter.normalConjugate K x
            (IrreducibleCharacter.trivial : IrreducibleCharacter K k) :=
        hx.symm
      _ = IrreducibleCharacter.trivial := by
        apply Subtype.ext
        ext y
        simp [IrreducibleCharacter.trivial_apply]
  · rintro ⟨hphi, hne⟩
    obtain ⟨chi, _, rfl⟩ := seqIndP.mp hphi
    apply (seqIndC1P (k := k) K).mpr
    refine ⟨chi, ?_, rfl⟩
    intro hchi
    subst chi
    exact hne rfl

/-- Finset-removal form of `seqIndC1_filter`, source `seqIndC1_rem`. -/
theorem seqIndC1_rem {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal] :
    seqIndD (k := k) K ⊤ ⊥ =
      (seqIndT K).erase
        (ClassFunction.induce K
          ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
            ClassFunction K k)) := by
  ext phi
  rw [seqIndC1_filter (k := k) K]
  simp [and_comm]

/-! ## Contragredients and the integral difference lattice -/

/-- Universe-polymorphic evaluation of a finite sum of class functions. -/
private theorem ClassFunction.finset_sum_apply_split
    {G : Type u} {k : Type v} [Group G] [Field k]
    {I : Type*} (s : Finset I) (f : I → ClassFunction G k) (g : G) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- Universe-polymorphic form of pullback-along-inversion commuting with
induction.  The Section 1 lemma currently identifies the group and
coefficient-field universes; this local form keeps the two independent. -/
private theorem ClassFunction.inverseLinear_induce_split
    {G : Type u} {k : Type v} [Group G] [Field k]
    [Fintype G] [CharZero k]
    (H : Subgroup G) [Fintype H] (f : ClassFunction H k) :
    ClassFunction.inverseLinear (ClassFunction.induce H f) =
      ClassFunction.induce H (ClassFunction.inverseLinear f) := by
  classical
  ext g
  rw [ClassFunction.inverseLinear_apply,
    ClassFunction.induce_apply_formula,
    ClassFunction.induce_apply_formula]
  apply congrArg ((Nat.card H : k)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x⁻¹ * g * x ∈ H
  · have hxinv : x⁻¹ * g⁻¹ * x ∈ H := by
      have heq : (x⁻¹ * g * x)⁻¹ = x⁻¹ * g⁻¹ * x := by group
      rw [← heq]
      exact H.inv_mem hx
    rw [dif_pos hxinv, dif_pos hx, ClassFunction.inverseLinear_apply]
    apply congrArg f
    apply Subtype.ext
    change x⁻¹ * g⁻¹ * x = (x⁻¹ * g * x)⁻¹
    group
  · have hxinv : x⁻¹ * g⁻¹ * x ∉ H := by
      intro hxinv
      apply hx
      have heq : (x⁻¹ * g⁻¹ * x)⁻¹ = x⁻¹ * g * x := by group
      rw [← heq]
      exact H.inv_mem hxinv
    rw [dif_neg hxinv, dif_neg hx]

/-- Pullback along inversion does not change the translation kernel of a
class function.  For a class function, right translation by an element is
equivalent to left translation by that element, and inversion exchanges
left translation by `a` with right translation by `a⁻¹`. -/
theorem ClassFunction.translationKernel_inverseLinear
    {G : Type u} {k : Type v} [Group G] [Field k]
    (f : ClassFunction G k) :
    ClassFunction.translationKernel (ClassFunction.inverseLinear f) =
      ClassFunction.translationKernel f := by
  ext a
  constructor
  · intro ha
    have hainv :=
      (ClassFunction.translationKernel
        (ClassFunction.inverseLinear f)).inv_mem ha
    have hright (x : G) : f (x * a) = f x := by
      have hx := hainv x⁻¹
      simpa only [ClassFunction.inverseLinear_apply, inv_inv, mul_inv_rev]
        using hx
    intro x
    calc
      f (a * x) = f (x * a) := by
        simpa [mul_assoc] using
          ClassFunction.conj_apply f a (x * a)
      _ = f x := hright x
  · intro ha
    have hainv := (ClassFunction.translationKernel f).inv_mem ha
    intro x
    change f ((a * x)⁻¹) = f x⁻¹
    calc
      f ((a * x)⁻¹) = f (x⁻¹ * a⁻¹) := by rw [mul_inv_rev]
      _ = f (a⁻¹ * x⁻¹) := by
        simpa [mul_assoc] using
          ClassFunction.conj_apply f x⁻¹ (a⁻¹ * x⁻¹)
      _ = f x⁻¹ := hainv x⁻¹

/-- Coercion of the contragredient irreducible character is pullback of its
class function along inversion. -/
@[simp]
theorem ClassFunction.inverseLinear_irreducible
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (chi : IrreducibleCharacter G k) :
    ClassFunction.inverseLinear (chi : ClassFunction G k) =
      (IrreducibleCharacter.dual chi : ClassFunction G k) := by
  ext g
  simp [IrreducibleCharacter.dual_apply]

/-- Every kernel layer is closed under contragredient duality. -/
theorem seqInd_inverse_mem {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (H M : Subgroup K)
    {phi : ClassFunction G k} (hphi : phi ∈ seqIndD (k := k) K H M) :
    ClassFunction.inverseLinear phi ∈ seqIndD (k := k) K H M := by
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  apply seqIndP.mpr
  refine ⟨IrreducibleCharacter.dual chi, ?_, ?_⟩
  · rw [mem_Iirr_kerD (k := k)] at hchi ⊢
    have hker :
        ClassFunction.translationKernel
            (IrreducibleCharacter.dual chi : ClassFunction K k) =
          ClassFunction.translationKernel (chi : ClassFunction K k) := by
      rw [← ClassFunction.inverseLinear_irreducible,
        ClassFunction.translationKernel_inverseLinear]
    simpa only [hker] using hchi
  · rw [ClassFunction.inverseLinear_induce_split,
      ClassFunction.inverseLinear_irreducible]

/-- Source `seqInd_conjC_subset1`, stated without importing the later
coherence vocabulary: the layer is contained in the indicated nontrivial
layer and is closed under contragredients. -/
theorem seqInd_conjC_subset1 {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G)
    (H₀ H M : Subgroup K) (hHH₀ : H ≤ H₀) :
    ((↑(seqIndD (k := k) K H M) : Set (ClassFunction G k)) ⊆
        ↑(seqIndD (k := k) K H₀ ⊥)) ∧
      ∀ phi ∈ seqIndD (k := k) K H M,
        ClassFunction.inverseLinear phi ∈ seqIndD (k := k) K H M := by
  refine ⟨?_, ?_⟩
  · exact seqIndS (k := k) K
      (Iirr_kerDS (k := k) bot_le hHH₀)
  · intro phi hphi
    exact seqInd_inverse_mem (k := k) K H M hphi

/-- Source `seqInd_sub_aut_zchar`: the difference between a selected
induced character and any coefficient twist has an explicit integral
preimage on the same family and is supported on `K\{1}`. -/
theorem seqInd_sub_aut_zchar {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (sigma : k ≃+* k) (K : Subgroup G) [K.Normal]
    (H M : Subgroup K) {phi : ClassFunction G k}
    (hphi : phi ∈ seqIndD (k := k) K H M) :
    ∃ z : SeqIndLattice K (Iirr_kerD (k := k) H M),
      seqIndRealize K (Iirr_kerD (k := k) H M) z =
          phi - ClassFunction.mapRingHom sigma.toRingHom phi ∧
        seqIndRealize K (Iirr_kerD (k := k) H M) z ∈
          ClassFunction.supportedOn (subgroupNonidentity K) := by
  let psi := ClassFunction.mapRingHom sigma.toRingHom phi
  have hpsi : psi ∈ seqIndD (k := k) K H M :=
    cfAut_seqInd (k := k) sigma K H M hphi
  let p : {xi : ClassFunction G k //
      xi ∈ seqInd K (Iirr_kerD (k := k) H M)} := ⟨phi, hphi⟩
  let q : {xi : ClassFunction G k //
      xi ∈ seqInd K (Iirr_kerD (k := k) H M)} := ⟨psi, hpsi⟩
  let z : SeqIndLattice K (Iirr_kerD (k := k) H M) :=
    Finsupp.single p 1 - Finsupp.single q 1
  refine ⟨z, ?_, ?_⟩
  · simp [z, p, q, psi]
  · have hz : seqIndRealize K (Iirr_kerD (k := k) H M) z =
        phi - psi := by simp [z, p, q]
    rw [hz, ClassFunction.mem_supportedOn_iff]
    intro x hx
    by_cases hxK : x ∈ K
    · have hx1 : x = 1 := by
        by_contra hx1
        exact hx ⟨hxK, hx1⟩
      subst x
      obtain ⟨n, hn⟩ := Cnat_seqInd1 K hphi
      change phi 1 - sigma (phi 1) = 0
      rw [hn, map_natCast, sub_self]
    · have hphi0 := ClassFunction.eq_zero_of_mem_supportedOn
          (seqInd_on K hphi) hxK
      have hpsi0 := ClassFunction.eq_zero_of_mem_supportedOn
          (seqInd_on K hpsi) hxK
      simp [ClassFunction.sub_apply, hphi0, hpsi0]

/-! ## Basic consequences for a kernel layer -/

/-- A proper interval of normal kernel subgroups contains an inducing
irreducible and hence gives a nonempty induced layer. -/
theorem seqIndD_nonempty {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G)
    (H M : Subgroup K) [H.Normal] [M.Normal] (hMH : M < H) :
    (seqIndD (k := k) K H M).Nonempty := by
  have hrel1 : M.relIndex H ≠ 1 := by
    intro hone
    exact hMH.not_ge (Subgroup.relIndex_eq_one.mp hone)
  have hfactor : (((M.relIndex H : ℕ) : k) - 1) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hrel1
  have hsumne :
      (∑ chi ∈ Iirr_kerD (k := k) H M, chi 1 ^ 2) ≠ 0 := by
    rw [sum_Iirr_kerD_square (k := k) H M hMH.le]
    exact mul_ne_zero
      (Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite) hfactor
  have hX : (Iirr_kerD (k := k) H M).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsumne
    simpa using hsumne
  obtain ⟨chi, hchi⟩ := hX
  exact ⟨ClassFunction.induce K (chi : ClassFunction K k),
    seqIndP.mpr ⟨chi, hchi, rfl⟩⟩

/-- Every kernel layer is contained in the nontrivial layer. -/
theorem seqInd_sub {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (H M : Subgroup K) :
    seqIndD (k := k) K H M ⊆
      seqIndD (k := k) K (⊤ : Subgroup K) ⊥ :=
  seqIndS (k := k) K
    (Iirr_kerDS (k := k) (A₁ := M) (A₂ := ⊥)
      (B₁ := H) (B₂ := ⊤) bot_le le_top)

/-- Members of a kernel layer are orthogonal to the character induced from
the trivial character. -/
theorem seqInd_ortho_Ind1 {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (H M : Subgroup K) {phi : ClassFunction G k}
    (hphi : phi ∈ seqIndD (k := k) K H M) :
    characterPairing phi
      (ClassFunction.induce K
        ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
          ClassFunction K k)) = 0 := by
  obtain ⟨chi, hchi, hphi_eq⟩ :=
    (seqIndC1P (k := k) K).mp
      (seqInd_sub (k := k) K H M hphi)
  rw [hphi_eq]
  apply ClassFunction.not_cfclass_Ind_ortho (k := k) K chi
    (IrreducibleCharacter.trivial : IrreducibleCharacter K k)
  intro horbit
  rw [MulAction.mem_orbit_iff] at horbit
  obtain ⟨x, hx⟩ := horbit
  apply hchi
  calc
    chi =
        IrreducibleCharacter.normalConjugate K x
          (IrreducibleCharacter.trivial : IrreducibleCharacter K k) :=
      hx.symm
    _ = IrreducibleCharacter.trivial := by
      apply Subtype.ext
      ext y
      simp [IrreducibleCharacter.trivial_apply]

/-- The normalized subgroup-uniform class function, source `'1_K`. -/
def subgroupUniform {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) : ClassFunction G k :=
  (K.index : k)⁻¹ •
    ClassFunction.induce K
      ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
        ClassFunction K k)

/-- Members of a kernel layer are orthogonal to the subgroup-uniform class
function. -/
theorem seqInd_ortho_cfuni {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (H M : Subgroup K) {phi : ClassFunction G k}
    (hphi : phi ∈ seqIndD (k := k) K H M) :
    characterPairing phi (subgroupUniform (k := k) K) = 0 := by
  change characterPairing phi
    ((K.index : k)⁻¹ •
      ClassFunction.induce K
        ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
          ClassFunction K k)) = 0
  rw [characterPairing_smul_right,
    seqInd_ortho_Ind1 (k := k) K H M hphi, mul_zero]

/-- Members of a kernel layer are orthogonal to the ambient trivial
character. -/
theorem seqInd_ortho_1 {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (H M : Subgroup K) {phi : ClassFunction G k}
    (hphi : phi ∈ seqIndD (k := k) K H M) :
    characterPairing phi
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
          ClassFunction G k) = 0 := by
  obtain ⟨chi, hchi, hphi_eq⟩ :=
    (seqIndC1P (k := k) K).mp
      (seqInd_sub (k := k) K H M hphi)
  rw [hphi_eq]
  rw [ClassFunction.frobeniusReciprocity]
  have hres : ClassFunction.restrict K
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G k) :
        ClassFunction G k) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
        ClassFunction K k) := by
    ext x
    simp [IrreducibleCharacter.trivial_apply]
  rw [hres]
  exact IrreducibleCharacter.characterPairing_eq_zero hchi

/-! ## The degree-square identity -/

/-- Bundle the irreducible character carried by a member of a normal
conjugacy orbit. -/
private def irreducibleOfNormalOrbit
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal] (chi : IrreducibleCharacter K k)
    (xi : ClassFunction.normalOrbit K (chi : ClassFunction K k)) :
    IrreducibleCharacter K k :=
  ⟨xi.1, by
    obtain ⟨x, hx⟩ := xi.property
    rw [← hx]
    exact ClassFunction.isIrreducibleCharacter_normalConjugate K x chi⟩

/-- If `X` is stable under ambient conjugation, the characters of `X`
inducing to `Ind chi` are exactly the normal conjugates of `chi`. -/
private def normalOrbitEquivInducingFiber
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (X : Finset (IrreducibleCharacter K k))
    (hstable : ∀ eta ∈ X, ∀ x : G, eta.normalConjugate K x ∈ X)
    (chi : IrreducibleCharacter K k) (hchi : chi ∈ X) :
    ClassFunction.normalOrbit K (chi : ClassFunction K k) ≃
      {eta : IrreducibleCharacter K k //
        eta ∈ X.filter
          (fun psi : IrreducibleCharacter K k ↦
            ClassFunction.induce K (psi : ClassFunction K k) =
              ClassFunction.induce K (chi : ClassFunction K k))} where
  toFun xi := by
    let eta := irreducibleOfNormalOrbit K chi xi
    refine ⟨eta, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · obtain ⟨x, hx⟩ := xi.property
      have heta : eta = chi.normalConjugate K x := by
        apply Subtype.ext
        exact hx.symm
      rw [heta]
      exact hstable chi hchi x
    · obtain ⟨x, hx⟩ := xi.property
      have heta : eta = chi.normalConjugate K x := by
        apply Subtype.ext
        exact hx.symm
      rw [heta, IrreducibleCharacter.coe_normalConjugate,
        ClassFunction.induce_normalConjugate]
  invFun eta := by
    refine ⟨(eta.1 : ClassFunction K k), ?_⟩
    have heq := (Finset.mem_filter.mp eta.property).2
    obtain ⟨x, hx⟩ :=
      (ClassFunction.cfclass_Ind_eq_iff (k := k) K chi eta.1).mp heq.symm
    exact ⟨x, hx⟩
  left_inv xi := by
    apply Subtype.ext
    rfl
  right_inv eta := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Orbit-fiber form of the degree-square calculation.  This is the
structural heart of source `sum_seqIndD_square`. -/
private theorem sum_seqInd_square_aux
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (X : Finset (IrreducibleCharacter K k))
    (hstable : ∀ eta ∈ X, ∀ x : G, eta.normalConjugate K x ∈ X) :
    (∑ phi ∈ seqInd (k := k) K X,
        phi 1 ^ 2 / characterPairing phi phi) =
      (K.index : k) * ∑ chi ∈ X, chi 1 ^ 2 := by
  unfold seqInd
  calc
    (∑ phi ∈ Finset.image
        (fun chi : IrreducibleCharacter K k ↦
          ClassFunction.induce K (chi : ClassFunction K k)) X,
        phi 1 ^ 2 / characterPairing phi phi) =
        ∑ chi ∈ X,
          (K.index : k) * ((chi : ClassFunction K k) 1) ^ 2 := by
      refine Finset.sum_image'
        (f := fun phi : ClassFunction G k ↦
          phi 1 ^ 2 / characterPairing phi phi)
        (g := fun psi : IrreducibleCharacter K k ↦
          ClassFunction.induce K (psi : ClassFunction K k))
        (s := X)
        (fun psi : IrreducibleCharacter K k ↦
          (K.index : k) * ((psi : ClassFunction K k) 1) ^ 2) ?_
      intro chi hchi
      have hone := congrArg (fun f : ClassFunction K k ↦ f 1)
        (ClassFunction.scaled_cfResInd_sum_cfclass (k := k) K chi)
      have hsum_apply :
          ((∑ xi : ClassFunction.normalOrbit K
                (chi : ClassFunction K k),
              (xi : ClassFunction K k) 1 • (xi : ClassFunction K k)) :
              ClassFunction K k) 1 =
            ∑ xi : ClassFunction.normalOrbit K
                (chi : ClassFunction K k),
              (xi : ClassFunction K k) 1 *
                (xi : ClassFunction K k) 1 := by
        change
          (∑ xi ∈ (Finset.univ : Finset
              (ClassFunction.normalOrbit K
                (chi : ClassFunction K k))),
              (xi : ClassFunction K k) 1 •
                (xi : ClassFunction K k)) 1 =
            ∑ xi ∈ (Finset.univ : Finset
              (ClassFunction.normalOrbit K
                (chi : ClassFunction K k))),
              (xi : ClassFunction K k) 1 *
                (xi : ClassFunction K k) 1
        rw [ClassFunction.finset_sum_apply_split]
        simp only [ClassFunction.smul_apply, smul_eq_mul]
      have hone' :
          (ClassFunction.induce K (chi : ClassFunction K k) 1 /
              characterPairing
                (ClassFunction.induce K (chi : ClassFunction K k))
                (ClassFunction.induce K (chi : ClassFunction K k))) *
              ClassFunction.induce K (chi : ClassFunction K k) 1 =
            (K.index : k) *
              ∑ xi : ClassFunction.normalOrbit K
                  (chi : ClassFunction K k),
                (xi : ClassFunction K k) 1 *
                  (xi : ClassFunction K k) 1 := by
        simpa only [ClassFunction.smul_apply, smul_eq_mul,
          ClassFunction.restrict_apply, Subgroup.coe_one, hsum_apply]
          using hone
      let fiber : Finset (IrreducibleCharacter K k) :=
        X.filter
          (fun psi : IrreducibleCharacter K k ↦
            ClassFunction.induce K (psi : ClassFunction K k) =
              ClassFunction.induce K (chi : ClassFunction K k))
      let e : ClassFunction.normalOrbit K (chi : ClassFunction K k) ≃
          fiber := normalOrbitEquivInducingFiber K X hstable chi hchi
      have horbit :
          (∑ xi : ClassFunction.normalOrbit K
              (chi : ClassFunction K k),
            (xi : ClassFunction K k) 1 ^ 2) =
            Finset.sum
              (X.filter
                (fun psi : IrreducibleCharacter K k ↦
                  ClassFunction.induce K (psi : ClassFunction K k) =
                    ClassFunction.induce K (chi : ClassFunction K k)))
              (fun psi : IrreducibleCharacter K k ↦
                ((psi : ClassFunction K k) 1) ^ 2) := by
        calc
          (∑ xi : ClassFunction.normalOrbit K
              (chi : ClassFunction K k),
              (xi : ClassFunction K k) 1 ^ 2) =
              ∑ psi : fiber,
                ((psi.1 : IrreducibleCharacter K k) :
                  ClassFunction K k) 1 ^ 2 := by
            apply Fintype.sum_equiv e
            intro xi
            rfl
          _ = Finset.sum
              (X.filter
                (fun psi : IrreducibleCharacter K k ↦
                  ClassFunction.induce K (psi : ClassFunction K k) =
                    ClassFunction.induce K (chi : ClassFunction K k)))
              (fun psi : IrreducibleCharacter K k ↦
                ((psi : ClassFunction K k) 1) ^ 2) := by
            simpa only [fiber] using
              (Finset.sum_coe_sort fiber
                (fun psi : IrreducibleCharacter K k ↦
                  ((psi : ClassFunction K k) 1) ^ 2))
      calc
        ClassFunction.induce K (chi : ClassFunction K k) 1 ^ 2 /
              characterPairing
                (ClassFunction.induce K (chi : ClassFunction K k))
                (ClassFunction.induce K (chi : ClassFunction K k)) =
            (ClassFunction.induce K (chi : ClassFunction K k) 1 /
              characterPairing
                (ClassFunction.induce K (chi : ClassFunction K k))
                (ClassFunction.induce K (chi : ClassFunction K k))) *
              ClassFunction.induce K (chi : ClassFunction K k) 1 := by
          ring
        _ = (K.index : k) *
              ∑ xi : ClassFunction.normalOrbit K
                (chi : ClassFunction K k),
                (xi : ClassFunction K k) 1 ^ 2 := by
          simpa only [pow_two] using hone'
        _ = (K.index : k) *
              Finset.sum
                (X.filter
                  (fun psi : IrreducibleCharacter K k ↦
                    ClassFunction.induce K (psi : ClassFunction K k) =
                      ClassFunction.induce K (chi : ClassFunction K k)))
                (fun psi : IrreducibleCharacter K k ↦
                  ((psi : ClassFunction K k) 1) ^ 2) := by
          rw [horbit]
        _ = Finset.sum
              (X.filter
                (fun psi : IrreducibleCharacter K k ↦
                  ClassFunction.induce K (psi : ClassFunction K k) =
                    ClassFunction.induce K (chi : ClassFunction K k)))
              (fun psi : IrreducibleCharacter K k ↦
                (K.index : k) *
                  ((psi : ClassFunction K k) 1) ^ 2) := by
          rw [Finset.mul_sum]
    _ = (K.index : k) * ∑ chi ∈ X, chi 1 ^ 2 := by
      rw [Finset.mul_sum]

/-- Source `sum_seqIndD_square`: the degree-square sum over the distinct
inductions in a stable kernel layer. -/
theorem sum_seqIndD_square
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (H M : Subgroup K)
    [((H.map K.subtype : Subgroup G)).Normal]
    [((M.map K.subtype : Subgroup G)).Normal]
    (hMH : M ≤ H) :
    (∑ phi ∈ seqIndD (k := k) K H M,
        phi 1 ^ 2 / characterPairing phi phi) =
      (K.index : k) *
        ((H.index : k) * (((M.relIndex H : ℕ) : k) - 1)) := by
  letI : H.Normal := Subgroup.Normal.of_map_subtype
    (inferInstance : (H.map K.subtype).Normal)
  letI : M.Normal := Subgroup.Normal.of_map_subtype
    (inferInstance : (M.map K.subtype).Normal)
  have hstable : ∀ chi ∈ Iirr_kerD (k := k) H M, ∀ x : G,
      chi.normalConjugate K x ∈ Iirr_kerD (k := k) H M := by
    intro chi hchi x
    apply (mem_seqInd (k := k) K H M (chi.normalConjugate K x)).mp
    rw [IrreducibleCharacter.coe_normalConjugate,
      ClassFunction.induce_normalConjugate]
    exact (mem_seqInd (k := k) K H M chi).mpr hchi
  calc
    (∑ phi ∈ seqIndD (k := k) K H M,
        phi 1 ^ 2 / characterPairing phi phi) =
        (K.index : k) *
          ∑ chi ∈ Iirr_kerD (k := k) H M, chi 1 ^ 2 :=
      sum_seqInd_square_aux (k := k) K
        (Iirr_kerD (k := k) H M) hstable
    _ = (K.index : k) *
        ((H.index : k) * (((M.relIndex H : ℕ) : k) - 1)) := by
      rw [sum_Iirr_kerD_square (k := k) H M hMH]

/-! ## Odd-order consequences -/

/-- In odd ambient order, every member of a kernel layer is orthogonal to
its contragredient. -/
theorem seqInd_conjC_ortho {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (hodd : Odd (Nat.card G)) (H M : Subgroup K)
    {phi : ClassFunction G k}
    (hphi : phi ∈ seqIndD (k := k) K H M) :
    characterPairing phi (ClassFunction.inverseLinear phi) = 0 := by
  have hphi_top :
      phi ∈ seqIndD (k := k) K (⊤ : Subgroup K) ⊥ :=
    seqInd_sub (k := k) K H M hphi
  obtain ⟨chi, hchi, hphi_eq⟩ :=
    (seqIndC1P (k := k) K).mp hphi_top
  rw [hphi_eq]
  letI : Invertible (Nat.card K : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hinvchi : ClassFunction.inverseLinear
        (chi : ClassFunction K k) =
      (IrreducibleCharacter.dual chi : ClassFunction K k) := by
    ext x
    rw [ClassFunction.inverseLinear_apply,
      IrreducibleCharacter.dual_apply]
  rw [ClassFunction.inverseLinear_induce_split K, hinvchi]
  rcases ClassFunction.cfclass_Ind_cases K chi
      (IrreducibleCharacter.dual chi) with horbit | hortho
  · obtain ⟨x, hx⟩ := horbit.1
    have hdual_normalConjugate :
        IrreducibleCharacter.dual (chi.normalConjugate K x) =
          (IrreducibleCharacter.dual chi).normalConjugate K x := by
      ext y
      simp only [IrreducibleCharacter.dual_apply,
        IrreducibleCharacter.coe_normalConjugate,
        ClassFunction.normalConjugate_apply]
      apply congrArg chi
      apply Subtype.ext
      simp
    have hdualconj :
        (IrreducibleCharacter.dual chi).normalConjugate K x = chi := by
      calc
        _ = IrreducibleCharacter.dual (chi.normalConjugate K x) :=
          hdual_normalConjugate.symm
        _ = IrreducibleCharacter.dual
            (IrreducibleCharacter.dual chi) := by
          apply congrArg IrreducibleCharacter.dual
          apply Subtype.ext
          exact hx
        _ = chi := IrreducibleCharacter.dual_dual chi
    have hsquare : ClassFunction.normalConjugate K (x ^ 2)
          (chi : ClassFunction K k) = (chi : ClassFunction K k) := by
      rw [pow_two, ClassFunction.normalConjugate_mul]
      calc
        ClassFunction.normalConjugate K x
            (ClassFunction.normalConjugate K x
              (chi : ClassFunction K k)) =
            ClassFunction.normalConjugate K x
              (IrreducibleCharacter.dual chi : ClassFunction K k) :=
          congrArg (ClassFunction.normalConjugate K x) hx
        _ = (chi : ClassFunction K k) := congrArg Subtype.val hdualconj
    have hxfix : ClassFunction.normalConjugate K x
          (chi : ClassFunction K k) = (chi : ClassFunction K k) := by
      have hxpow : (x ^ 2) ^ (Nat.card G).gcdB 2 = x := by
        let hcop : (Nat.card G).Coprime 2 := hodd.coprime_two_right
        change (powCoprime hcop).symm (powCoprime hcop x) = x
        exact (powCoprime hcop).symm_apply_apply x
      rw [← ClassFunction.mem_inertia_iff] at hsquare ⊢
      rw [← hxpow]
      exact (ClassFunction.inertia K
        (chi : ClassFunction K k)).zpow_mem hsquare _
    have hself : IrreducibleCharacter.dual chi = chi := by
      apply Subtype.ext
      exact hx.symm.trans hxfix
    have hoddK : Odd (Nat.card K) := by
      apply Odd.of_dvd_nat hodd
      simpa only [Subgroup.card_top] using
        (Subgroup.card_dvd_of_le
          (show K ≤ (⊤ : Subgroup G) from le_top))
    exact (hchi ((odd_eq_conj_irr1 hoddK chi).mp hself)).elim
  · exact hortho.2

/-- No member of a kernel layer in odd order is self-contragredient. -/
theorem seqInd_conjC_neq {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (hodd : Odd (Nat.card G)) (H M : Subgroup K)
    {phi : ClassFunction G k}
    (hphi : phi ∈ seqIndD (k := k) K H M) :
    ClassFunction.inverseLinear phi ≠ phi := by
  intro heq
  have hz := seqInd_conjC_ortho (k := k) K hodd H M hphi
  rw [heq] at hz
  exact (cfnorm_seqInd_neq0 K hphi) hz

/-- Source `seqInd_notReal`: the layer has no inversion-fixed member. -/
theorem seqInd_notReal {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (hodd : Odd (Nat.card G)) (H M : Subgroup K) :
    ¬ ∃ phi ∈ seqIndD (k := k) K H M,
      ClassFunction.inverseLinear phi = phi := by
  rintro ⟨phi, hphi, hreal⟩
  exact seqInd_conjC_neq (k := k) K hodd H M hphi hreal

/-- A nonempty layer in odd order contains at least a contragredient pair. -/
theorem seqInd_nontrivial {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (hodd : Odd (Nat.card G)) (H M : Subgroup K)
    {phi : ClassFunction G k}
    (hphi : phi ∈ seqIndD (k := k) K H M) :
    2 ≤ (seqIndD (k := k) K H M).card := by
  have hinv : ClassFunction.inverseLinear phi ∈
      seqIndD (k := k) K H M :=
    seqInd_inverse_mem (k := k) K H M hphi
  have hne : ClassFunction.inverseLinear phi ≠ phi :=
    seqInd_conjC_neq (k := k) K hodd H M hphi
  let T : Finset (ClassFunction G k) :=
    {phi, ClassFunction.inverseLinear phi}
  have hT : T ⊆ seqIndD (k := k) K H M := by
    intro psi hpsi
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hpsi
    rcases hpsi with rfl | rfl
    · exact hphi
    · exact hinv
  have hcard := Finset.card_le_card hT
  simpa [T, hne, hne.symm] using hcard

/-- An ambient irreducible member and its contragredient form an
orthonormal pair. -/
theorem seqInd_conjC_ortho2 {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (hodd : Odd (Nat.card G)) (H M : Subgroup K)
    (chi : IrreducibleCharacter G k)
    (hchi : (chi : ClassFunction G k) ∈
      seqIndD (k := k) K H M) :
    characterPairing (chi : ClassFunction G k) (chi : ClassFunction G k) = 1 ∧
      characterPairing
          (IrreducibleCharacter.dual chi : ClassFunction G k)
          (IrreducibleCharacter.dual chi : ClassFunction G k) = 1 ∧
      characterPairing (chi : ClassFunction G k)
          (IrreducibleCharacter.dual chi : ClassFunction G k) = 0 ∧
      characterPairing
          (IrreducibleCharacter.dual chi : ClassFunction G k)
          (chi : ClassFunction G k) = 0 := by
  have hortho : characterPairing (chi : ClassFunction G k)
      (IrreducibleCharacter.dual chi : ClassFunction G k) = 0 := by
    simpa only [← ClassFunction.inverseLinear_irreducible] using
      seqInd_conjC_ortho (k := k) K hodd H M hchi
  exact ⟨IrreducibleCharacter.characterPairing_self chi,
    IrreducibleCharacter.characterPairing_self
      (IrreducibleCharacter.dual chi), hortho,
    (characterPairing_comm
      (IrreducibleCharacter.dual chi : ClassFunction G k)
      (chi : ClassFunction G k)).trans hortho⟩

/-- Ambient irreducible characters whose class functions lie in a selected
kernel layer. -/
def seqIndDIrreducibles {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (H M : Subgroup K) :
    Finset (IrreducibleCharacter G k) :=
  Finset.univ.filter fun chi ↦
    (chi : ClassFunction G k) ∈ seqIndD (k := k) K H M

/-- Source `seqInd_nontrivial_irr`: if a layer contains an ambient
irreducible, it contains at least that irreducible and its distinct dual. -/
theorem seqInd_nontrivial_irr {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (hodd : Odd (Nat.card G)) (H M : Subgroup K)
    (chi : IrreducibleCharacter G k)
    (hchi : (chi : ClassFunction G k) ∈
      seqIndD (k := k) K H M) :
    2 ≤ (seqIndDIrreducibles (k := k) K H M).card := by
  have hdual : (IrreducibleCharacter.dual chi : ClassFunction G k) ∈
      seqIndD (k := k) K H M := by
    rw [← ClassFunction.inverseLinear_irreducible]
    exact seqInd_inverse_mem (k := k) K H M hchi
  have hne : IrreducibleCharacter.dual chi ≠ chi := by
    intro heq
    apply seqInd_conjC_neq (k := k) K hodd H M hchi
    rw [ClassFunction.inverseLinear_irreducible, heq]
  let T : Finset (IrreducibleCharacter G k) :=
    {chi, IrreducibleCharacter.dual chi}
  have hT : T ⊆ seqIndDIrreducibles (k := k) K H M := by
    intro psi hpsi
    simp only [seqIndDIrreducibles, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hpsi
    rcases hpsi with rfl | rfl
    · exact hchi
    · exact hdual
  have hcard := Finset.card_le_card hT
  simpa [T, hne, hne.symm] using hcard

/-- Source `sum_seqIndC1_square`, the degree-square identity for all
nontrivial inducing irreducibles. -/
theorem sum_seqIndC1_square
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal] :
    (∑ phi ∈ seqIndD (k := k) K (⊤ : Subgroup K) ⊥,
        phi 1 ^ 2 / characterPairing phi phi) =
      (K.index : k) * ((Nat.card K : k) - 1) := by
  letI : (((⊤ : Subgroup K).map K.subtype : Subgroup G)).Normal := by
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using
      (inferInstance : K.Normal)
  letI : (((⊥ : Subgroup K).map K.subtype : Subgroup G)).Normal := by
    rw [Subgroup.map_bot]
    infer_instance
  simpa only [Subgroup.index_top, Nat.cast_one, one_mul,
    Subgroup.relIndex_bot_left, Subgroup.card_top] using
      (sum_seqIndD_square (k := k) K (⊤ : Subgroup K) ⊥ bot_le)

end

end Submission.OddOrder.PF
