import Submission.OddOrder.MathlibSupport.CoprimeElementaryAbelianComplement
import Submission.OddOrder.MathlibSupport.FrattiniPGroup
import Submission.OddOrder.MathlibSupport.InvariantSubgroupAction
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.RingTheory.FiniteLength

/-!
# The opening structure theorem for the Wielandt fixed-point argument

The first lemma of `wielandt_fixpoint.v` decomposes an abelian `p`-group
acted on coprimely into invariant homocyclic factors whose Frattini
quotients are irreducible.  This file sets up the Lean-facing form of those
notions.  In the exponent-`p` branch Maschke's theorem gives the factors
directly as the simple summands of the conjugation module; the general case
then follows the source induction through the last nonzero power subgroup.

The general-exponent step is the induction through the last nonzero power
subgroup used in the Coq proof.  The public decomposition records ambient
multiplicative subgroups, while the elementary branch transports the simple
group-algebra summands through the submodule/subgroup order isomorphism.
Thus the same package can express both branches and `sSupIndep` records the
internal direct-product datum.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative MonoidAlgebra

universe u v

/-- A finite `p`-group is homocyclic when it is a finite direct power of
one cyclic group of order `p ^ e`.  The positive exponent excludes the
degenerate presentation by copies of `ZMod 1`; the trivial group is still
covered by taking no copies. -/
def IsHomocyclicPGroup (p : ℕ) (H : Type*) [Group H] : Prop :=
  ∃ (d e : ℕ), 0 < e ∧
    Nonempty (H ≃* (Fin d → Multiplicative (ZMod (p ^ e))))

/-- Homocyclicity is invariant under group isomorphism. -/
theorem IsHomocyclicPGroup.of_mulEquiv
    {p : ℕ} {H K : Type*} [Group H] [Group K]
    (hH : IsHomocyclicPGroup p H) (e : K ≃* H) :
    IsHomocyclicPGroup p K := by
  rcases hH with ⟨d, n, hn, ⟨h⟩⟩
  exact ⟨d, n, hn, ⟨e.trans h⟩⟩

/-- Reindex a finite direct product of groups. -/
def MulEquiv.piCongrLeft
    {ι κ : Type*} (e : ι ≃ κ) (M : Type*) [Group M] :
    (ι → M) ≃* (κ → M) where
  toFun x j := x (e.symm j)
  invFun x i := x (e i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_mul' _ _ := rfl

/-- An isomorphism maps the Frattini subgroup onto the Frattini subgroup. -/
theorem _root_.MulEquiv.map_frattini
    {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (frattini H).map e.toMonoidHom = frattini K := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective e.surjective
  · have h : frattini K ≤ (frattini H).comap e.symm.toMonoidHom :=
      frattini_le_comap_frattini_of_surjective e.symm.surjective
    intro x hx
    have hx' : e.symm x ∈ frattini H := h hx
    exact ⟨e.symm x, hx', by simp⟩

/-- Every finite abelian group of exponent dividing the prime `p` is
homocyclic (with cyclic factors of order `p`). -/
theorem isHomocyclicPGroup_of_pow_prime
    {H : Type*} [Group H] [Finite H] [IsMulCommutative H]
    {p : ℕ} [Fact p.Prime] (hpow : ∀ x : H, x ^ p = 1) :
    IsHomocyclicPGroup p H := by
  letI hmod : Module (ZMod p) (Additive H) :=
    AddCommGroup.zmodModule fun x ↦ by
      change x.toMul ^ p = 1
      exact hpow x.toMul
  letI : Fintype (Additive H) := Fintype.ofFinite (Additive H)
  letI hfin : Module.Finite (ZMod p) (Additive H) := by
    exact ⟨⟨Finset.univ, by
      rw [Finset.coe_univ, Submodule.span_univ]⟩⟩
  letI hfree : Module.Free (ZMod p) (Additive H) := by infer_instance
  letI hsrc : StrongRankCondition (ZMod p) := by infer_instance
  let b := @Module.finBasis (ZMod p) (Additive H)
    inferInstance inferInstance hmod hfree hsrc hfin
  let eadd : Additive H ≃+ (Fin (Module.finrank (ZMod p) (Additive H)) → ZMod p) :=
    b.equivFun.toAddEquiv
  refine ⟨Module.finrank (ZMod p) (Additive H), 1, Nat.zero_lt_succ 0, ?_⟩
  refine ⟨?_⟩
  rw [pow_one]
  exact
    (AddEquiv.toMultiplicativeRight eadd).trans
      (MulEquiv.piMultiplicative
        (fun _ : Fin (Module.finrank (ZMod p) (Additive H)) ↦ ZMod p))

variable {E : Type u} {A : Type v}
variable [Group E] [Finite E] [Group A] [Finite A]
variable {p : ℕ} [Fact p.Prime] [IsMulCommutative E]

/-- Invariance of a subgroup under an action by automorphisms. -/
def IsInvariantUnderMulAutAction (f : A →* MulAut E) (B : Subgroup E) : Prop :=
  ∀ a : A, B.map (f a).toMonoidHom = B

/-- Group-theoretic irreducibility on `B / Φ(B)`.  Subgroups of that
quotient correspond to invariant subgroups of `B` containing the image of
its Frattini subgroup, so this formulation avoids introducing a second
quotient representation merely to state the source property. -/
def ActsIrreduciblyOnFrattiniQuotient
    (f : A →* MulAut E) (B : Subgroup E) : Prop :=
  IsInvariantUnderMulAutAction f B ∧
    ∀ C : Subgroup E, C ≤ B → IsInvariantUnderMulAutAction f C →
      (frattini B).map B.subtype ≤ C →
      C = (frattini B).map B.subtype ∨ C = B

/-- The intrinsic version of irreducibility on a Frattini quotient. -/
def ActsIrreduciblyOnOwnFrattiniQuotient
    {H : Type*} [Group H] (f : A →* MulAut H) : Prop :=
  ∀ C : Subgroup H, IsInvariantUnderMulAutAction f C →
    frattini H ≤ C → C = frattini H ∨ C = ⊤

/-- The ambient-subgroup and intrinsic formulations agree after restricting
the action to the invariant subgroup. -/
theorem actsIrreduciblyOnFrattiniQuotient_iff_restrict
    (f : A →* MulAut E) (B : Subgroup E)
    (hB : IsInvariantUnderMulAutAction f B) :
    ActsIrreduciblyOnFrattiniQuotient f B ↔
      ActsIrreduciblyOnOwnFrattiniQuotient
        (restrictMulAutHom B f hB) := by
  let fB := restrictMulAutHom B f hB
  constructor
  · rintro ⟨_hB, hmin⟩ C hC hPhi
    have hCmap : C.map B.subtype ≤ B := Subgroup.map_subtype_le C
    have hCinv :
        IsInvariantUnderMulAutAction f (C.map B.subtype) := by
      intro a
      exact map_subtype_invariant_of_restrictMulAutHom B C f hB hC a
    have hPhiMap : (frattini B).map B.subtype ≤ C.map B.subtype :=
      Subgroup.map_mono hPhi
    rcases hmin (C.map B.subtype) hCmap hCinv hPhiMap with h | h
    · left
      exact (Subgroup.map_injective B.subtype_injective) (by
        simpa using h)
    · right
      apply Subgroup.map_injective B.subtype_injective
      have htop : (⊤ : Subgroup B).map B.subtype = B :=
        (MonoidHom.range_eq_map B.subtype).symm.trans B.range_subtype
      simpa only [htop] using h
  · intro hown
    refine ⟨hB, ?_⟩
    intro C hCB hC hPhi
    let CB : Subgroup B := C.subgroupOf B
    have hCBinv : IsInvariantUnderMulAutAction fB CB := by
      intro a
      exact subgroupOf_map_restrictMulAutHom_eq B C hCB f hB hC a
    have hPhiB : frattini B ≤ CB := by
      intro x hx
      exact hPhi ⟨x, hx, rfl⟩
    rcases hown CB hCBinv hPhiB with h | h
    · left
      calc
        C = CB.map B.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hCB).symm
        _ = (frattini B).map B.subtype := congrArg (Subgroup.map B.subtype) h
    · right
      calc
        C = CB.map B.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hCB).symm
        _ = (⊤ : Subgroup B).map B.subtype := congrArg (Subgroup.map B.subtype) h
        _ = B := (MonoidHom.range_eq_map B.subtype).symm.trans B.range_subtype

/-- Intrinsic Frattini irreducibility transports across an equivariant
group isomorphism. -/
theorem ActsIrreduciblyOnOwnFrattiniQuotient.of_mulEquiv
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    (fH : A →* MulAut H) (fK : A →* MulAut K)
    (e : H ≃* K)
    (he : ∀ a : A, ∀ x : H, e (fH a x) = fK a (e x))
    (hH : ActsIrreduciblyOnOwnFrattiniQuotient fH) :
    ActsIrreduciblyOnOwnFrattiniQuotient fK := by
  intro C hC hPhi
  let D : Subgroup H := C.comap e.toMonoidHom
  have hD : IsInvariantUnderMulAutAction fH D := by
    intro a
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      change e (fH a x) ∈ C
      rw [he]
      have hmap : fK a (e x) ∈ C.map (fK a).toMonoidHom :=
        ⟨e x, hx, rfl⟩
      rwa [hC a] at hmap
    · rw [Subgroup.card_map_of_injective (fH a).injective]
  have hPhiD : frattini H ≤ D := by
    intro x hx
    apply hPhi
    have : e x ∈ (frattini H).map e.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [e.map_frattini] at this
  rcases hH D hD hPhiD with h | h
  · left
    calc
      C = D.map e.toMonoidHom := by
        symm
        exact Subgroup.map_comap_eq_self_of_surjective e.surjective C
      _ = (frattini H).map e.toMonoidHom :=
        congrArg (Subgroup.map e.toMonoidHom) h
      _ = frattini K := e.map_frattini
  · right
    calc
      C = D.map e.toMonoidHom := by
        symm
        exact Subgroup.map_comap_eq_self_of_surjective e.surjective C
      _ = (⊤ : Subgroup H).map e.toMonoidHom :=
        congrArg (Subgroup.map e.toMonoidHom) h
      _ = ⊤ := by simp

/-- A source-faithful package for the factors supplied by the opening
Wielandt structure lemma.  The blocks are ambient subgroups rather than
prime-field submodules: this is essential in the general-exponent branch,
where `Additive E` is not a `ZMod p`-module. -/
structure CoprimeActionHomocyclicDecomposition
    (p : ℕ) (f : A →* MulAut E) where
  blocks : Set (Subgroup E)
  finite_blocks : blocks.Finite
  independent : sSupIndep blocks
  spans : sSup blocks = ⊤
  homocyclic : ∀ B ∈ blocks, IsHomocyclicPGroup p B
  invariant : ∀ B ∈ blocks, IsInvariantUnderMulAutAction f B
  irreducible_frattini : ∀ B ∈ blocks,
    ActsIrreduciblyOnFrattiniQuotient f B

/-- The relative form used while assembling the induction step. -/
structure CoprimeActionHomocyclicDecompositionBelow
    (p : ℕ) (f : A →* MulAut E) (P : Subgroup E) where
  blocks : Set (Subgroup E)
  finite_blocks : blocks.Finite
  independent : sSupIndep blocks
  spans : sSup blocks = P
  homocyclic : ∀ B ∈ blocks, IsHomocyclicPGroup p B
  invariant : ∀ B ∈ blocks, IsInvariantUnderMulAutAction f B
  irreducible_frattini : ∀ B ∈ blocks,
    ActsIrreduciblyOnFrattiniQuotient f B

/-- Injective group homomorphisms preserve independence of an indexed
family of subgroups. -/
theorem iSupIndep_subgroup_map_of_injective
    {H K : Type*} [Group H] [Group K]
    {ι : Type*} (B : ι → Subgroup H) (g : H →* K)
    (hg : Function.Injective g) (hB : iSupIndep B) :
    iSupIndep (fun i ↦ (B i).map g) := by
  intro i
  simpa only [Subgroup.map_iSup] using
    Subgroup.disjoint_map hg (hB i)

/-- Mapping a supremum of subgroups is the supremum of their images. -/
theorem sSup_subgroup_map
    {H K : Type*} [Group H] [Group K]
    (s : Set (Subgroup H)) (g : H →* K) :
    (sSup s).map g = sSup ((fun B ↦ B.map g) '' s) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, sSup_le_iff]
    intro B hB
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨B, hB, rfl⟩
  · rw [sSup_le_iff]
    rintro C ⟨B, hB, rfl⟩
    exact Subgroup.map_mono (le_sSup hB)

/-! ### Invariant power subgroups and quotient actions -/

/-- The subgroup of `p ^ n`th powers in a commutative group.  Using the
range, rather than a generated subgroup, is possible because the power map
is a homomorphism in the abelian kernel of the Wielandt argument. -/
def abelianPowerSubgroup (p n : ℕ) (E : Type u)
    [Group E] [IsMulCommutative E] : Subgroup E :=
  (powMonoidHom (p ^ n) : E →* E).range

/-- The omega-one subgroup of an abelian group. -/
def abelianOmegaOne (p : ℕ) (E : Type u)
    [Group E] [IsMulCommutative E] : Subgroup E :=
  (powMonoidHom p : E →* E).ker

@[simp]
theorem mem_abelianPowerSubgroup_iff (p n : ℕ) (x : E) :
    x ∈ abelianPowerSubgroup p n E ↔ ∃ y : E, y ^ (p ^ n) = x := by
  rfl

@[simp]
theorem mem_abelianOmegaOne_iff (p : ℕ) (x : E) :
    x ∈ abelianOmegaOne p E ↔ x ^ p = 1 := by
  rfl

/-- Every automorphism preserves every power subgroup. -/
theorem abelianPowerSubgroup_invariant
    (f : A →* MulAut E) (p n : ℕ) :
    IsInvariantUnderMulAutAction f (abelianPowerSubgroup p n E) := by
  intro a
  exact MulEquiv.map_range_powMonoidHom (f a) (p ^ n)

/-- Every automorphism preserves omega one. -/
theorem abelianOmegaOne_invariant
    (f : A →* MulAut E) (p : ℕ) :
    IsInvariantUnderMulAutAction f (abelianOmegaOne p E) := by
  intro a
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change (f a x) ^ p = 1
    simpa using congrArg (f a) hx
  · rintro x hx
    refine ⟨(f a)⁻¹ x, ?_, by simp⟩
    change ((f a)⁻¹ x) ^ p = 1
    simpa using congrArg (f a).symm hx

/-- The exponent of a finite `p`-group is a power of `p`. -/
theorem IsPGroup.exponent_eq_prime_pow
    (hE : IsPGroup p E) :
    ∃ n : ℕ, Monoid.exponent E = p ^ n := by
  obtain ⟨m, hm⟩ := hE.exists_card_eq
  have hdvd : Monoid.exponent E ∣ p ^ m := by
    rw [← hm]
    exact Group.exponent_dvd_nat_card
  obtain ⟨n, _hnm, hn⟩ :=
    (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  exact ⟨n, hn⟩

/-- A nontrivial finite `p`-group has exponent `p ^ (n+1)`. -/
theorem IsPGroup.exists_exponent_eq_prime_pow_succ
    (hE : IsPGroup p E) [Nontrivial E] :
    ∃ n : ℕ, Monoid.exponent E = p ^ (n + 1) := by
  obtain ⟨k, hk⟩ := IsPGroup.exponent_eq_prime_pow hE
  have hk0 : k ≠ 0 := by
    intro hkzero
    have : Monoid.exponent E = 1 := by simpa [hkzero] using hk
    exact (Monoid.one_lt_exponent (G := E)).ne' this
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  exact ⟨n, by simpa [Nat.succ_eq_add_one] using hk⟩

/-- The finite-abelian classification specialized to a `p`-group of known
exponent. -/
theorem exists_prime_power_cyclic_decomposition
    (hE : IsPGroup p E) (m : ℕ)
    (hexp : Monoid.exponent E = p ^ m) :
    ∃ (ι : Type) (_ : Fintype ι) (k : ι → ℕ),
      (∀ i, 0 < k i) ∧ (∀ i, k i ≤ m) ∧
      Nonempty (E ≃* ((i : ι) → Multiplicative (ZMod (p ^ k i)))) := by
  classical
  obtain ⟨ι, hι, q, hq, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite E
  letI : Fintype ι := hι
  have hqdiv : ∀ i, q i ∣ Monoid.exponent E := by
    intro i
    have hi : q i =
        orderOf (e.symm (Pi.mulSingle i (Multiplicative.ofAdd 1))) := by
      simpa only [MulEquiv.orderOf_eq, orderOf_piMulSingle,
        orderOf_ofAdd_eq_addOrderOf] using (ZMod.addOrderOf_one (q i)).symm
    exact hi ▸ Monoid.order_dvd_exponent _
  have hk : ∀ i, ∃ k ≤ m, q i = p ^ k := by
    intro i
    apply (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
    simpa [hexp] using hqdiv i
  choose k hkm hkq using hk
  have hkpos : ∀ i, 0 < k i := by
    intro i
    apply Nat.pos_of_ne_zero
    intro hki
    have : q i = 1 := by simpa [hki] using hkq i
    exact (hq i).ne' this
  refine ⟨ι, inferInstance, k, hkpos, hkm, ?_⟩
  have hqk : q = fun i ↦ p ^ k i := funext hkq
  subst q
  exact ⟨e⟩

/-- The last nonzero power subgroup has exponent `p`. -/
theorem abelianPowerSubgroup_pow_prime_eq_one
    (n : ℕ) (hexp : Monoid.exponent E = p ^ (n + 1))
    (x : abelianPowerSubgroup p n E) : x ^ p = 1 := by
  apply Subtype.ext
  rcases x.property with ⟨y, hy⟩
  change (x : E) ^ p = 1
  rw [← hy]
  change (y ^ (p ^ n)) ^ p = 1
  rw [← pow_mul, ← pow_succ]
  simpa [Nat.succ_eq_add_one, hexp] using Monoid.pow_exponent_eq_one y

/-- The last power subgroup is nontrivial when the ambient exponent is
`p ^ (n+1)`. -/
theorem abelianPowerSubgroup_ne_bot_of_exponent
    (n : ℕ) (hexp : Monoid.exponent E = p ^ (n + 1)) :
    abelianPowerSubgroup p n E ≠ ⊥ := by
  obtain ⟨x, hx⟩ :=
    Monoid.exists_orderOf_eq_exponent
      (Monoid.ExponentExists.of_finite (G := E))
  have hxpow : x ^ (p ^ n) ≠ 1 := by
    intro hpow
    have hdvd : orderOf x ∣ p ^ n := orderOf_dvd_of_pow_eq_one hpow
    rw [hx, hexp, Nat.pow_dvd_pow_iff_le_right
      (Fact.out : p.Prime).one_lt] at hdvd
    omega
  intro hbot
  have hmem : x ^ (p ^ n) ∈ abelianPowerSubgroup p n E :=
    ⟨x, rfl⟩
  rw [hbot] at hmem
  exact hxpow (Subgroup.mem_bot.mp hmem)

/-- The last power subgroup lies in omega one. -/
theorem abelianPowerSubgroup_le_omegaOne
    (n : ℕ) (hexp : Monoid.exponent E = p ^ (n + 1)) :
    abelianPowerSubgroup p n E ≤ abelianOmegaOne p E := by
  intro x hx
  change x ^ p = 1
  exact congrArg Subtype.val
    (abelianPowerSubgroup_pow_prime_eq_one n hexp ⟨x, hx⟩)

/-- The omega/last-power criterion for a finite abelian `p`-group to be
homocyclic.  This is the Lean form of MathComp's
`Ohm1_homocyclicP`, in the direction used by Wielandt's induction. -/
theorem isHomocyclicPGroup_of_omegaOne_eq_lastPower
    (hE : IsPGroup p E) [Nontrivial E]
    (n : ℕ) (hexp : Monoid.exponent E = p ^ (n + 1))
    (homega : abelianOmegaOne p E = abelianPowerSubgroup p n E) :
    IsHomocyclicPGroup p E := by
  classical
  obtain ⟨ι, hι, k, hkpos, hkle, ⟨e⟩⟩ :=
    exists_prime_power_cyclic_decomposition hE (n + 1) hexp
  letI : Fintype ι := hι
  have hkmax : ∀ i, k i = n + 1 := by
    intro i
    apply le_antisymm (hkle i)
    apply Nat.succ_le_of_lt
    by_contra hnot
    have hkin : k i ≤ n := Nat.le_of_not_gt hnot
    let g : (j : ι) → Multiplicative (ZMod (p ^ k j)) :=
      Pi.mulSingle i (Multiplicative.ofAdd 1)
    let w := g ^ (p ^ (k i - 1))
    let x : E := e.symm w
    have hwpow : w ^ p = 1 := by
      ext j
      by_cases hji : j = i
      · subst j
        change p • (w i).toAdd = 0
        simp only [w, g, Pi.pow_apply, toAdd_pow, Pi.mulSingle_eq_same]
        simp only [toAdd_ofAdd, nsmul_eq_mul, mul_one]
        rw [← Nat.cast_mul, ← pow_succ',
          Nat.sub_add_cancel (hkpos i), ZMod.natCast_self]
      · change p • (w j).toAdd = 0
        simp [w, g, Pi.mulSingle, hji]
    have hxomega : x ∈ abelianOmegaOne p E := by
      rw [mem_abelianOmegaOne_iff]
      apply e.injective
      rw [map_pow, e.apply_symm_apply, map_one]
      exact hwpow
    have hxpower : x ∈ abelianPowerSubgroup p n E := by
      rw [← homega]
      exact hxomega
    rcases hxpower with ⟨y, hy⟩
    change y ^ (p ^ n) = x at hy
    have hey : (e y) ^ (p ^ n) = w := by
      calc
        (e y) ^ (p ^ n) = e (y ^ (p ^ n)) := (map_pow e y (p ^ n)).symm
        _ = e x := congrArg e hy
        _ = w := e.apply_symm_apply w
    have hey_i := congrArg (fun z ↦ (z i).toAdd) hey
    have hleft : (((e y) ^ (p ^ n)) i).toAdd = 0 := by
      simp only [Pi.pow_apply, toAdd_pow, nsmul_eq_mul]
      rw [show (((p ^ n : ℕ) : ZMod (p ^ k i))) = 0 by
        rw [ZMod.natCast_eq_zero_iff]
        exact (Nat.pow_dvd_pow_iff_le_right
          (Fact.out : p.Prime).one_lt).mpr hkin]
      simp
    have hright : (w i).toAdd ≠ 0 := by
      have hcast : (((p ^ (k i - 1) : ℕ) : ZMod (p ^ k i))) ≠ 0 := by
        intro hz
        have hdvd : p ^ k i ∣ p ^ (k i - 1) :=
          (ZMod.natCast_eq_zero_iff _ _).mp hz
        have hle : k i ≤ k i - 1 :=
          (Nat.pow_dvd_pow_iff_le_right
            (Fact.out : p.Prime).one_lt).mp hdvd
        have hkEq : k i = (k i - 1) + 1 :=
          (Nat.sub_add_cancel (hkpos i)).symm
        rw [hkEq] at hle
        exact (Nat.not_succ_le_self _) hle
      simpa only [w, g, Pi.pow_apply, toAdd_pow,
        Pi.mulSingle_eq_same, toAdd_ofAdd, nsmul_eq_mul, mul_one] using hcast
    apply hright
    rw [← hey_i]
    exact hleft
  have hkfun : k = fun _ : ι ↦ n + 1 := funext hkmax
  subst k
  refine ⟨Fintype.card ι, n + 1, Nat.zero_lt_succ n, ?_⟩
  refine ⟨e.trans ?_⟩
  exact MulEquiv.piCongrLeft (Fintype.equivFin ι)
    (Multiplicative (ZMod (p ^ (n + 1))))

/-- For a finite abelian `p`-group the Frattini subgroup is precisely the
subgroup of `p`th powers. -/
theorem frattini_eq_abelianPowerSubgroup_one
    (hE : IsPGroup p E) :
    frattini E = abelianPowerSubgroup p 1 E := by
  let P : Subgroup E := abelianPowerSubgroup p 1 E
  have hPle : P ≤ frattini E := by
    rintro _ ⟨x, rfl⟩
    simpa using IsPGroup.pow_prime_mem_frattini hE x
  letI : P.Normal := Subgroup.normal_of_comm P
  have hQpow : ∀ x : E ⧸ P, x ^ p = 1 := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P x
    change QuotientGroup.mk' P (x ^ p) = 1
    exact (QuotientGroup.eq_one_iff (x ^ p)).mpr ⟨x, by simp⟩
  have hPhiQ : frattini (E ⧸ P) = ⊥ :=
    IsPGroup.frattini_eq_bot_of_isMulCommutative_of_pow_prime hQpow
  have hle : frattini E ≤
      (frattini (E ⧸ P)).comap (QuotientGroup.mk' P) :=
    frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective P)
  rw [hPhiQ, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hle
  exact le_antisymm hle hPle

/-- If omega one is the last power subgroup, then the kernel of the last
power map is the first power subgroup.  The proof is the finite-cardinality
calculation implicit in the Coq `Ohm`/`Mho` identities. -/
theorem ker_lastPower_eq_abelianPowerSubgroup_one
    (n : ℕ) (hexp : Monoid.exponent E = p ^ (n + 1))
    (homega : abelianOmegaOne p E = abelianPowerSubgroup p n E) :
    (powMonoidHom (p ^ n) : E →* E).ker =
      abelianPowerSubgroup p 1 E := by
  let f1 : E →* E := powMonoidHom p
  let fn : E →* E := powMonoidHom (p ^ n)
  let O : Subgroup E := f1.ker
  let P : Subgroup E := f1.range
  let K : Subgroup E := fn.ker
  have hPK : P ≤ K := by
    rintro _ ⟨x, rfl⟩
    change (x ^ p) ^ (p ^ n) = 1
    rw [← pow_mul, ← pow_succ']
    simpa [Nat.succ_eq_add_one, hexp] using Monoid.pow_exponent_eq_one x
  have hhomega : O = fn.range := by
    simpa [O, fn, f1, abelianOmegaOne, abelianPowerSubgroup] using homega
  have hPindex : P.index = Nat.card O := by
    simpa [P, O, f1] using (Subgroup.index_range (f := f1))
  have hOindex : O.index = Nat.card K := by
    rw [hhomega]
    simpa [K, fn] using (Subgroup.index_range (f := fn))
  have hPcard : Nat.card P * Nat.card O = Nat.card E := by
    rw [← hPindex]
    exact P.card_mul_index
  have hOcard : Nat.card O * Nat.card K = Nat.card E := by
    rw [← hOindex]
    exact O.card_mul_index
  have hcard : Nat.card P = Nat.card K := by
    apply Nat.mul_left_cancel (Nat.card_pos (α := O))
    calc
      Nat.card O * Nat.card P = Nat.card P * Nat.card O := Nat.mul_comm _ _
      _ = Nat.card E := hPcard
      _ = Nat.card O * Nat.card K := hOcard.symm
  have hKP : K = P :=
    (Subgroup.eq_of_le_of_card_ge hPK hcard.ge).symm
  simpa [K, P, fn, f1, abelianPowerSubgroup] using hKP

/-- Minimal nontrivial invariant subgroups exist inside every nontrivial
invariant subgroup of a finite group. -/
theorem exists_minimal_invariant_subgroup_le
    (f : A →* MulAut E) (L : Subgroup E)
    (hLne : L ≠ ⊥) (hL : IsInvariantUnderMulAutAction f L) :
    ∃ B : Subgroup E,
      B ≤ L ∧ B ≠ ⊥ ∧ IsInvariantUnderMulAutAction f B ∧
      ∀ C : Subgroup E, C ≤ B → C ≠ ⊥ →
        IsInvariantUnderMulAutAction f C → C = B := by
  let P : Subgroup E → Prop := fun B ↦
    B ≤ L ∧ B ≠ ⊥ ∧ IsInvariantUnderMulAutAction f B
  have hPL : P L := ⟨le_rfl, hLne, hL⟩
  obtain ⟨B, _hBL, hBmin⟩ := Finite.exists_le_minimal hPL
  refine ⟨B, hBmin.1.1, hBmin.1.2.1, hBmin.1.2.2, ?_⟩
  intro C hCB hCne hC
  have hPC : P C :=
    ⟨hCB.trans hBmin.1.1, hCne, hC⟩
  exact le_antisymm hCB (hBmin.eq_of_ge hPC hCB).le

/-- The quotient automorphism induced by an automorphism preserving a
normal subgroup. -/
noncomputable def invariantQuotientMulAut
    (N : Subgroup E) [N.Normal]
    (e : MulAut E) (hN : N.map e.toMonoidHom = N) :
    MulAut (E ⧸ N) := by
  have he : N ≤ N.comap e.toMonoidHom := by
    intro x hx
    change e x ∈ N
    have : e x ∈ N.map e.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hN] at this
  have heinv : N ≤ N.comap e.symm.toMonoidHom := by
    intro x hx
    change e.symm x ∈ N
    have hxmap : x ∈ N.map e.toMonoidHom := by
      rw [hN]
      exact hx
    rcases hxmap with ⟨y, hy, rfl⟩
    simpa using hy
  let q := QuotientGroup.map N N e.toMonoidHom he
  let qinv := QuotientGroup.map N N e.symm.toMonoidHom heinv
  exact MonoidHom.toMulEquiv q qinv
    (by
      apply MonoidHom.ext
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
      simp [q, qinv])
    (by
      apply MonoidHom.ext
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
      simp [q, qinv])

@[simp]
theorem invariantQuotientMulAut_apply_mk
    (N : Subgroup E) [N.Normal]
    (e : MulAut E) (hN : N.map e.toMonoidHom = N) (x : E) :
    invariantQuotientMulAut N e hN (QuotientGroup.mk' N x) =
      QuotientGroup.mk' N (e x) := by
  rfl

/-- An invariant normal subgroup lets an action descend to the quotient. -/
noncomputable def invariantQuotientMulAutHom
    (N : Subgroup E) [N.Normal]
    (f : A →* MulAut E) (hN : IsInvariantUnderMulAutAction f N) :
    A →* MulAut (E ⧸ N) where
  toFun a := invariantQuotientMulAut N (f a) (hN a)
  map_one' := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    simp only [invariantQuotientMulAut_apply_mk, map_one,
      MulAut.one_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    simp only [invariantQuotientMulAut_apply_mk, map_mul,
      MulAut.mul_apply]

@[simp]
theorem invariantQuotientMulAutHom_apply_mk
    (N : Subgroup E) [N.Normal]
    (f : A →* MulAut E) (hN : IsInvariantUnderMulAutAction f N)
    (a : A) (x : E) :
    invariantQuotientMulAutHom N f hN a (QuotientGroup.mk' N x) =
      QuotientGroup.mk' N (f a x) := by
  rfl

/-- Images of invariant subgroups are invariant for the quotient action. -/
theorem map_quotient_invariant
    (N : Subgroup E) [N.Normal]
    (f : A →* MulAut E) (hN : IsInvariantUnderMulAutAction f N)
    (B : Subgroup E) (hB : IsInvariantUnderMulAutAction f B) :
    IsInvariantUnderMulAutAction (invariantQuotientMulAutHom N f hN)
      (B.map (QuotientGroup.mk' N)) := by
  intro a
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, ⟨b, hb, rfl⟩, rfl⟩
    have hfb : f a b ∈ B := by
      have : f a b ∈ B.map (f a).toMonoidHom := ⟨b, hb, rfl⟩
      rwa [hB a] at this
    refine ⟨f a b, hfb, ?_⟩
    exact (invariantQuotientMulAutHom_apply_mk N f hN a b).symm
  · exact (Subgroup.card_map_of_injective
      (K := B.map (QuotientGroup.mk' N))
      (f := (invariantQuotientMulAutHom N f hN a).toMonoidHom)
      (invariantQuotientMulAutHom N f hN a).injective).ge

/-- Preimages of invariant quotient subgroups are invariant upstairs. -/
theorem comap_quotient_invariant
    (N : Subgroup E) [N.Normal]
    (f : A →* MulAut E) (hN : IsInvariantUnderMulAutAction f N)
    (C : Subgroup (E ⧸ N))
    (hC : IsInvariantUnderMulAutAction
      (invariantQuotientMulAutHom N f hN) C) :
    IsInvariantUnderMulAutAction f (C.comap (QuotientGroup.mk' N)) := by
  intro a
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    change QuotientGroup.mk' N (f a x) ∈ C
    have hmap :
        invariantQuotientMulAutHom N f hN a
            (QuotientGroup.mk' N x) ∈
          C.map (invariantQuotientMulAutHom N f hN a).toMonoidHom :=
      ⟨QuotientGroup.mk' N x, hx, rfl⟩
    rw [hC a] at hmap
    exact hmap
  · rw [Subgroup.card_map_of_injective (f a).injective]

/-- Maschke's complement inside omega one, transported back to the ambient
abelian `p`-group.  This is the `U` chosen near the start of the Coq
induction. -/
theorem exists_invariant_complement_in_abelianOmegaOne
    (f : A →* MulAut E) (hpA : ¬p ∣ Nat.card A)
    (B : Subgroup E) (hBO : B ≤ abelianOmegaOne p E)
    (hB : IsInvariantUnderMulAutAction f B) :
    ∃ U : Subgroup E,
      U ≤ abelianOmegaOne p E ∧
      IsInvariantUnderMulAutAction f U ∧
      Disjoint B U ∧ B ⊔ U = abelianOmegaOne p E := by
  let O : Subgroup E := abelianOmegaOne p E
  have hO : IsInvariantUnderMulAutAction f O :=
    abelianOmegaOne_invariant f p
  let fO : A →* MulAut O := restrictMulAutHom O f hO
  let BO : Subgroup O := B.subgroupOf O
  have hBOinv : IsInvariantUnderMulAutAction fO BO := by
    intro a
    exact subgroupOf_map_restrictMulAutHom_eq O B hBO f hO hB a
  have hOpow : ∀ x : O, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    exact x.property
  obtain ⟨X, hcompl, hX⟩ :=
    exists_invariant_complement_of_coprime_mulAut_action
      hOpow fO hpA BO hBOinv
  let U : Subgroup E := X.map O.subtype
  have hUO : U ≤ O := Subgroup.map_subtype_le X
  have hU : IsInvariantUnderMulAutAction f U := by
    intro a
    exact map_subtype_invariant_of_restrictMulAutHom O X f hO hX a
  refine ⟨U, hUO, hU, ?_, ?_⟩
  · have hmap := Subgroup.disjoint_map O.subtype_injective hcompl.1
    have hBmap : BO.map O.subtype = B :=
      Subgroup.map_subgroupOf_eq_of_le hBO
    rw [hBmap] at hmap
    exact hmap
  · have hBmap : BO.map O.subtype = B :=
      Subgroup.map_subgroupOf_eq_of_le hBO
    have htopmap : (⊤ : Subgroup O).map O.subtype = O :=
      (MonoidHom.range_eq_map O.subtype).symm.trans O.range_subtype
    calc
      B ⊔ U = (BO ⊔ X).map O.subtype := by
        rw [Subgroup.map_sup, hBmap]
      _ = (⊤ : Subgroup O).map O.subtype :=
        congrArg (Subgroup.map O.subtype) hcompl.2.eq_top
      _ = O := htopmap

/-- Homocyclicity survives viewing a subgroup of an invariant subgroup as
an ambient subgroup. -/
theorem isHomocyclicPGroup_map_subtype
    (P : Subgroup E) (X : Subgroup P)
    (hX : IsHomocyclicPGroup p X) :
    IsHomocyclicPGroup p (X.map P.subtype) :=
  hX.of_mulEquiv
    (X.equivMapOfInjective P.subtype P.subtype_injective).symm

/-- Frattini irreducibility survives the same change of ambient group. -/
theorem actsIrreduciblyOnFrattiniQuotient_map_subtype
    (f : A →* MulAut E) (P : Subgroup E)
    (hP : IsInvariantUnderMulAutAction f P)
    (X : Subgroup P)
    (hX : ActsIrreduciblyOnFrattiniQuotient
      (restrictMulAutHom P f hP) X) :
    ActsIrreduciblyOnFrattiniQuotient f (X.map P.subtype) := by
  let fP := restrictMulAutHom P f hP
  let Y : Subgroup E := X.map P.subtype
  have hXinv : IsInvariantUnderMulAutAction fP X := hX.1
  have hYinv : IsInvariantUnderMulAutAction f Y := by
    intro a
    exact map_subtype_invariant_of_restrictMulAutHom P X f hP hXinv a
  let fX := restrictMulAutHom X fP hXinv
  let fY := restrictMulAutHom Y f hYinv
  let e : X ≃* Y :=
    X.equivMapOfInjective P.subtype P.subtype_injective
  have he : ∀ a : A, ∀ x : X, e (fX a x) = fY a (e x) := by
    intro a x
    apply Subtype.ext
    rfl
  have hownX : ActsIrreduciblyOnOwnFrattiniQuotient fX :=
    (actsIrreduciblyOnFrattiniQuotient_iff_restrict
      fP X hXinv).mp hX
  have hownY : ActsIrreduciblyOnOwnFrattiniQuotient fY :=
    hownX.of_mulEquiv fX fY e he
  exact (actsIrreduciblyOnFrattiniQuotient_iff_restrict
    f Y hYinv).mpr hownY

/-- A decomposition of an invariant subgroup, expressed using its own
subgroups, becomes a relative ambient decomposition after mapping along the
subtype inclusion. -/
noncomputable def CoprimeActionHomocyclicDecomposition.map_subtype
    (f : A →* MulAut E) (P : Subgroup E)
    (hP : IsInvariantUnderMulAutAction f P)
    (D : CoprimeActionHomocyclicDecomposition p
      (restrictMulAutHom P f hP)) :
    CoprimeActionHomocyclicDecompositionBelow p f P := by
  let m : Subgroup P → Subgroup E := fun X ↦ X.map P.subtype
  let blocks : Set (Subgroup E) := m '' D.blocks
  refine
    { blocks := blocks
      finite_blocks := D.finite_blocks.image m
      independent := ?_
      spans := ?_
      homocyclic := ?_
      invariant := ?_
      irreducible_frattini := ?_ }
  · let em : D.blocks ≃ blocks :=
      Equiv.Set.image m D.blocks
        (Subgroup.map_injective P.subtype_injective)
    have hind : iSupIndep (fun X : D.blocks ↦ m X) :=
      iSupIndep_subgroup_map_of_injective
        (fun X : D.blocks ↦ (X : Subgroup P)) P.subtype
        P.subtype_injective ((sSupIndep_iff D.blocks).mp D.independent)
    have heq : ((fun X : D.blocks ↦ m X) ∘ em.symm) =
        ((↑) : blocks → Subgroup E) := by
      funext B
      exact congrArg Subtype.val (em.apply_symm_apply B)
    rw [sSupIndep_iff]
    rw [← heq]
    exact hind.comp em.symm.injective
  · have hmap : (sSup D.blocks).map P.subtype = sSup blocks := by
      simpa [blocks, m] using sSup_subgroup_map D.blocks P.subtype
    rw [← hmap, D.spans]
    exact (MonoidHom.range_eq_map P.subtype).symm.trans P.range_subtype
  · rintro B ⟨X, hX, rfl⟩
    exact isHomocyclicPGroup_map_subtype P X (D.homocyclic X hX)
  · rintro B ⟨X, hX, rfl⟩
    intro a
    exact map_subtype_invariant_of_restrictMulAutHom P X f hP
      (D.invariant X hX) a
  · rintro B ⟨X, hX, rfl⟩
    exact actsIrreduciblyOnFrattiniQuotient_map_subtype
      f P hP X (D.irreducible_frattini X hX)

/-- Adjoin one complementary block to a relative decomposition.  This is
the final `D |: S` assembly in the Coq induction. -/
noncomputable def CoprimeActionHomocyclicDecompositionBelow.insert_complement
    (f : A →* MulAut E) (P D : Subgroup E)
    (R : CoprimeActionHomocyclicDecompositionBelow p f P)
    (hcompl : IsCompl D P) (hDne : D ≠ ⊥)
    (hDhomo : IsHomocyclicPGroup p D)
    (hDinv : IsInvariantUnderMulAutAction f D)
    (hDirr : ActsIrreduciblyOnFrattiniQuotient f D) :
    CoprimeActionHomocyclicDecomposition p f := by
  have hblockle : ∀ B ∈ R.blocks, B ≤ P := by
    intro B hB
    exact (le_sSup hB).trans_eq R.spans
  have hDnot : D ∉ R.blocks := by
    intro hDmem
    have hDP : D ≤ P := hblockle D hDmem
    apply hDne
    apply le_antisymm _ bot_le
    exact (le_inf le_rfl hDP).trans hcompl.1.le_bot
  refine
    { blocks := insert D R.blocks
      finite_blocks := R.finite_blocks.insert D
      independent := ?_
      spans := ?_
      homocyclic := ?_
      invariant := ?_
      irreducible_frattini := ?_ }
  · intro B hB
    rcases hB with rfl | hB
    · simpa [hDnot, R.spans] using hcompl.1
    · have hBD : B ≠ D := fun h ↦ hDnot (h ▸ hB)
      let T : Subgroup E := sSup (R.blocks \ {B})
      have hBT : Disjoint B T := R.independent hB
      have hTle : T ≤ P := by
        rw [sSup_le_iff]
        intro C hC
        exact hblockle C hC.1
      have hBTP : B ⊔ T ≤ P := sup_le (hblockle B hB) hTle
      have hBTD : Disjoint (B ⊔ T) D :=
        hcompl.1.symm.mono_left hBTP
      have hfinal : Disjoint B (T ⊔ D) :=
        hBT.disjoint_sup_right_of_disjoint_sup_left hBTD
      have hset : insert D R.blocks \ {B} =
          insert D (R.blocks \ {B}) := by
        ext C
        simp only [Set.mem_sdiff, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        constructor
        · rintro ⟨hCD | hCR, hCB⟩
          · exact Or.inl hCD
          · exact Or.inr ⟨hCR, hCB⟩
        · rintro (hCD | ⟨hCR, hCB⟩)
          · exact ⟨Or.inl hCD, fun hBC ↦ hBD (hBC.symm.trans hCD)⟩
          · exact ⟨Or.inr hCR, hCB⟩
      rw [hset, sSup_insert]
      simpa [T, sup_comm] using hfinal
  · simp [R.spans, hcompl.2.eq_top]
  · intro B hB
    rcases hB with rfl | hB
    · exact hDhomo
    · exact R.homocyclic B hB
  · intro B hB
    rcases hB with rfl | hB
    · exact hDinv
    · exact R.invariant B hB
  · intro B hB
    rcases hB with rfl | hB
    · exact hDirr
    · exact R.irreducible_frattini B hB

/-- A homocyclic group on which the action is irreducible contributes one
block. -/
noncomputable def coprimeActionHomocyclicDecomposition_single
    (f : A →* MulAut E)
    (hE : IsHomocyclicPGroup p E)
    (hirr : ActsIrreduciblyOnFrattiniQuotient f (⊤ : Subgroup E)) :
    CoprimeActionHomocyclicDecomposition p f := by
  refine
    { blocks := {(⊤ : Subgroup E)}
      finite_blocks := Set.finite_singleton ⊤
      independent := sSupIndep_singleton ⊤
      spans := by simp
      homocyclic := ?_
      invariant := ?_
      irreducible_frattini := ?_ }
  · rintro B rfl
    exact hE.of_mulEquiv Subgroup.topEquiv
  · rintro B rfl a
    exact Subgroup.map_top_of_surjective _ (f a).surjective
  · rintro B rfl
    exact hirr

/-- The empty decomposition of the trivial group. -/
noncomputable def coprimeActionHomocyclicDecomposition_of_subsingleton
    (f : A →* MulAut E) [Subsingleton E] :
    CoprimeActionHomocyclicDecomposition p f := by
  refine
    { blocks := ∅
      finite_blocks := Set.finite_empty
      independent := sSupIndep_empty
      spans := by
        rw [sSup_empty]
        exact Subsingleton.elim ⊥ ⊤
      homocyclic := by simp
      invariant := by simp
      irreducible_frattini := by simp }

section ElementaryAbelian

variable [Module (ZMod p) (Additive E)]

/-- The multiplicative subgroup underlying an invariant group-algebra
submodule of an elementary abelian action. -/
noncomputable def actionSubmoduleSubgroup
    (f : A →* MulAut E)
    (U : Submodule (MonoidAlgebra (ZMod p) A)
      (elementaryAbelianActionRepresentation E A p f).asModule) :
    Subgroup E :=
  elementaryAbelianGroupSubmoduleSubgroupOrderIso E p
    (U.restrictScalars (ZMod p))

@[simp]
theorem mem_actionSubmoduleSubgroup
    (f : A →* MulAut E)
    (U : Submodule (MonoidAlgebra (ZMod p) A)
      (elementaryAbelianActionRepresentation E A p f).asModule)
    (x : E) :
    x ∈ actionSubmoduleSubgroup f U ↔ Additive.ofMul x ∈ U :=
  Iff.rfl

/-- A group-algebra submodule gives an invariant multiplicative subgroup. -/
theorem actionSubmoduleSubgroup_invariant
    (f : A →* MulAut E)
    (U : Submodule (MonoidAlgebra (ZMod p) A)
      (elementaryAbelianActionRepresentation E A p f).asModule) :
    IsInvariantUnderMulAutAction f (actionSubmoduleSubgroup f U) := by
  intro a
  apply Subgroup.eq_of_le_of_card_ge
  · rintro y ⟨x, hx, rfl⟩
    change Additive.ofMul x ∈ U at hx
    change Additive.ofMul (f a x) ∈ U
    exact (Subrepresentation.ofSubmodule' U).apply_mem_toSubmodule a hx
  · rw [Subgroup.card_map_of_injective (f a).injective]

/-- Turn an invariant multiplicative subgroup back into its group-algebra
submodule. -/
noncomputable def invariantSubgroupSubmodule
    (f : A →* MulAut E) (C : Subgroup E)
    (hC : IsInvariantUnderMulAutAction f C) :
    Submodule (MonoidAlgebra (ZMod p) A)
      (elementaryAbelianActionRepresentation E A p f).asModule := by
  let σ : Subrepresentation (elementaryAbelianActionRepresentation E A p f) :=
    { toSubmodule :=
        (elementaryAbelianGroupSubmoduleSubgroupOrderIso E p).symm C
      apply_mem_toSubmodule := by
        intro a x hx
        change f a x.toMul ∈ C
        have hmap : f a x.toMul ∈ C.map (f a).toMonoidHom :=
          ⟨x.toMul, hx, rfl⟩
        rw [hC a] at hmap
        exact hmap }
  exact σ.asSubmodule

@[simp]
theorem mem_invariantSubgroupSubmodule
    (f : A →* MulAut E) (C : Subgroup E)
    (hC : IsInvariantUnderMulAutAction f C)
    (x : Additive E) :
    x ∈ invariantSubgroupSubmodule (p := p) f C hC ↔ x.toMul ∈ C :=
  Iff.rfl

@[simp]
theorem actionSubmoduleSubgroup_invariantSubgroupSubmodule
    (f : A →* MulAut E) (C : Subgroup E)
    (hC : IsInvariantUnderMulAutAction f C) :
    actionSubmoduleSubgroup f
      (invariantSubgroupSubmodule (p := p) f C hC) = C := by
  ext x
  rfl

@[simp]
theorem actionSubmoduleSubgroup_bot (f : A →* MulAut E) :
    actionSubmoduleSubgroup f
      (⊥ : Submodule (MonoidAlgebra (ZMod p) A)
        (elementaryAbelianActionRepresentation E A p f).asModule) = ⊥ := by
  ext x
  change Additive.ofMul x = 0 ↔ x = 1
  rfl

theorem actionSubmoduleSubgroup_eq_orderIso
    (f : A →* MulAut E)
    (U : Submodule (MonoidAlgebra (ZMod p) A)
      (elementaryAbelianActionRepresentation E A p f).asModule) :
    actionSubmoduleSubgroup f U =
      elementaryAbelianGroupSubmoduleSubgroupOrderIso E p
        (U.restrictScalars (ZMod p)) :=
  rfl

/-- Restriction from the group algebra to its coefficient ring preserves
independence of indexed submodule families. -/
theorem iSupIndep_submodule_restrictScalars
    {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]
    {I : Type*} (U : I → Submodule R M) (hU : iSupIndep U) :
    iSupIndep (fun i ↦ (U i).restrictScalars S) := by
  intro i
  have hi : Disjoint ((U i).restrictScalars S)
      ((⨆ (j) (_ : j ≠ i), U j).restrictScalars S) :=
    (Submodule.disjoint_restrictScalars_iff (S := S)).mpr (hU i)
  simpa only [Submodule.restrictScalars_iSup] using hi

/-- In the exponent-`p` case, a simple action submodule gives precisely an
irreducible Frattini factor in the group-theoretic sense. -/
theorem actionSubmoduleSubgroup_actsIrreduciblyOnFrattiniQuotient
    (f : A →* MulAut E) (hpow : ∀ x : E, x ^ p = 1)
    (U : Submodule (MonoidAlgebra (ZMod p) A)
      (elementaryAbelianActionRepresentation E A p f).asModule)
    (hU : IsSimpleModule (MonoidAlgebra (ZMod p) A) U) :
    ActsIrreduciblyOnFrattiniQuotient f (actionSubmoduleSubgroup f U) := by
  let B := actionSubmoduleSubgroup f U
  have hBpow : ∀ x : B, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    exact hpow x.1
  have hPhi : frattini B = ⊥ :=
    IsPGroup.frattini_eq_bot_of_isMulCommutative_of_pow_prime hBpow
  refine ⟨actionSubmoduleSubgroup_invariant f U, ?_⟩
  intro C hCB hC _hPhiC
  let V := invariantSubgroupSubmodule (p := p) f C hC
  have hVU : V ≤ U := by
    intro x hx
    have hxC : x.toMul ∈ C :=
      (mem_invariantSubgroupSubmodule (p := p) f C hC x).mp hx
    exact (mem_actionSubmoduleSubgroup f U x.toMul).mp (hCB hxC)
  have hAtom : IsAtom U := isSimpleModule_iff_isAtom.mp hU
  rcases hAtom.le_iff.mp hVU with hV | hV
  · left
    have hCbot : C = ⊥ := by
      calc
        C = actionSubmoduleSubgroup f V :=
          (actionSubmoduleSubgroup_invariantSubgroupSubmodule
            (p := p) f C hC).symm
        _ = actionSubmoduleSubgroup f ⊥ := congrArg (actionSubmoduleSubgroup f) hV
        _ = ⊥ := actionSubmoduleSubgroup_bot f
    change C = (frattini B).map B.subtype
    rw [hCbot, hPhi, Subgroup.map_bot]
  · right
    calc
      C = actionSubmoduleSubgroup f V :=
        (actionSubmoduleSubgroup_invariantSubgroupSubmodule
          (p := p) f C hC).symm
      _ = actionSubmoduleSubgroup f U := congrArg (actionSubmoduleSubgroup f) hV

/-- The subgroup attached to any action submodule is homocyclic in the
exponent-`p` case. -/
theorem actionSubmoduleSubgroup_isHomocyclicPGroup
    (f : A →* MulAut E) (hpow : ∀ x : E, x ^ p = 1)
    (U : Submodule (MonoidAlgebra (ZMod p) A)
      (elementaryAbelianActionRepresentation E A p f).asModule) :
    IsHomocyclicPGroup p (actionSubmoduleSubgroup f U) := by
  apply isHomocyclicPGroup_of_pow_prime
  intro x
  apply Subtype.ext
  exact hpow x.1

/-- The exponent-`p` branch of Coq
`coprime_act_abelian_pgroup_structure`: a coprime action on a finite
elementary abelian `p`-group splits into invariant homocyclic factors with
irreducible Frattini quotients. -/
noncomputable def coprime_act_abelian_pgroup_structure_of_exponent_prime
    (f : A →* MulAut E) (hpA : ¬p ∣ Nat.card A)
    (hpow : ∀ x : E, x ^ p = 1) :
    CoprimeActionHomocyclicDecomposition p f := by
  let ρ := elementaryAbelianActionRepresentation E A p f
  letI : NeZero (Nat.card A : ZMod p) :=
    NeZero.of_not_dvd (ZMod p) hpA
  letI : Representation.IsSemisimpleRepresentation ρ := by infer_instance
  letI : IsSemisimpleModule (MonoidAlgebra (ZMod p) A) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
      inferInstance
  letI : Module.Finite (ZMod p) ρ.asModule := by infer_instance
  letI : Module.Finite (MonoidAlgebra (ZMod p) A) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite
      (ZMod p) (MonoidAlgebra (ZMod p) A) ρ.asModule
  let hs : ∃ s : Set (Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule),
      s.Finite ∧ sSupIndep s ∧ sSup s = ⊤ ∧
        ∀ U ∈ s, IsSimpleModule (MonoidAlgebra (ZMod p) A) U :=
    ((IsSemisimpleModule.finite_tfae
      (R := MonoidAlgebra (ZMod p) A) (M := ρ.asModule)).out 0 4).mp
      (inferInstance : Module.Finite (MonoidAlgebra (ZMod p) A) ρ.asModule)
  let s := Classical.choose hs
  have hs_spec := Classical.choose_spec hs
  rcases hs_spec with ⟨hsfinite, hsindependent, hsspans, hssimple⟩
  let e := elementaryAbelianGroupSubmoduleSubgroupOrderIso E p
  let r : Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule →
      Submodule (ZMod p) (Additive E) :=
    fun U ↦ U.restrictScalars (ZMod p)
  let m : Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule →
      Subgroup E := fun U ↦ e (r U)
  let blocks : Set (Subgroup E) := m '' s
  refine
    { blocks := blocks
      finite_blocks := hsfinite.image m
      independent := ?_
      spans := ?_
      homocyclic := ?_
      invariant := ?_
      irreducible_frattini := ?_ }
  · have hm : Function.Injective m := by
      intro U V hUV
      apply Submodule.restrictScalars_injective (ZMod p)
        (MonoidAlgebra (ZMod p) A) ρ.asModule
      apply e.injective
      exact hUV
    let es : s ≃ blocks := Equiv.Set.image m s hm
    have hsindr : iSupIndep (fun U : s ↦ r (U :
        Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule)) :=
      iSupIndep_submodule_restrictScalars
        (fun U : s ↦ (U :
          Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule))
        ((sSupIndep_iff s).mp hsindependent)
    have hsind : iSupIndep (fun U : s ↦ m U) := by
      have hmapped := iSupIndep.map_orderIso e hsindr
      intro U
      simpa only [Function.comp_apply] using hmapped U
    have heq : ((fun U : s ↦ m (U :
        Submodule (MonoidAlgebra (ZMod p) A) ρ.asModule)) ∘ es.symm) =
        ((↑) : blocks → Subgroup E) := by
      funext B
      exact congrArg Subtype.val (es.apply_symm_apply B)
    rw [sSupIndep_iff]
    rw [← heq]
    exact hsind.comp es.symm.injective
  · change sSup (m '' s) = ⊤
    have hsets : m '' s = e '' (r '' s) := by
      ext B
      constructor
      · rintro ⟨U, hU, rfl⟩
        exact ⟨r U, ⟨U, hU, rfl⟩, rfl⟩
      · rintro ⟨V, ⟨U, hU, rfl⟩, rfl⟩
        exact ⟨U, hU, rfl⟩
    calc
      sSup (m '' s) = e (sSup (r '' s)) := by
        rw [hsets]
        exact (map_sSup e (r '' s)).symm
      _ = e (r (sSup s)) := by
        congr 1
        exact (Submodule.restrictScalars_sSup (ZMod p) s).symm
      _ = e (r ⊤) := congrArg (fun U ↦ e (r U)) hsspans
      _ = e ⊤ := by
        apply congrArg e
        exact Submodule.restrictScalars_top (ZMod p)
          (MonoidAlgebra (ZMod p) A) ρ.asModule
      _ = ⊤ := e.map_top
  · rintro B ⟨U, hU, rfl⟩
    change IsHomocyclicPGroup p (actionSubmoduleSubgroup f U)
    exact actionSubmoduleSubgroup_isHomocyclicPGroup f hpow U
  · rintro B ⟨U, hU, rfl⟩
    change IsInvariantUnderMulAutAction f (actionSubmoduleSubgroup f U)
    exact actionSubmoduleSubgroup_invariant f U
  · rintro B ⟨U, hU, rfl⟩
    change ActsIrreduciblyOnFrattiniQuotient f
      (actionSubmoduleSubgroup f U)
    exact actionSubmoduleSubgroup_actsIrreduciblyOnFrattiniQuotient
      f hpow U (hssimple U hU)

end ElementaryAbelian

end Submission.OddOrder.MathlibSupport
