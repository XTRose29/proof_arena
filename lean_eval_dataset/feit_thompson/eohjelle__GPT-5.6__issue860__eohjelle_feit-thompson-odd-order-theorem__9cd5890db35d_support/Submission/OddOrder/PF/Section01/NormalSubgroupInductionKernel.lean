import Submission.OddOrder.PF.Section01.InducedCharacterCompatibility
import Submission.OddOrder.PF.Section01.NormalSubgroupInductionConsequences

/-!
# Kernels of characters induced from a normal subgroup

This file begins Peterfalvi 1.6.  Its main result is a representation-level
form of 1.6(a), strengthened from irreducible characters to arbitrary
finite-dimensional representations: if `A ◁ G` and `A ≤ H`, then `A` acts
trivially on the representation induced from `H` exactly when it acts
trivially on the original representation.

The proof uses the function model of coinduction.  Normality ensures that
right translation by an element of `A` can be rewritten using the original
`H`-action; the finite-index induction--coinduction equivalence then transfers
the kernel calculation to induction.  We also port the adjacent source
consequence `cfInd_irr_eq1`, using the 1.5 induction-orbit theorem.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u v w

namespace RepresentationEquiv

variable {k : Type u} [Semiring k] {G : Type v} [Group G]
  {V W : Type w} [AddCommMonoid V] [Module k V]
  [AddCommMonoid W] [Module k W]
  {rho : Representation k G V} {sigma : Representation k G W}

/-- Equivalent representations have the same kernel. -/
theorem ker_eq (e : rho.Equiv sigma) : rho.ker = sigma.ker := by
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hg
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    change sigma g (e v) = e v
    calc
      sigma g (e v) = e (rho g v) :=
        (_root_.Representation.IntertwiningMap.isIntertwining
          (ρ := rho) (σ := sigma) (f := e.toIntertwiningMap) g v).symm
      _ = e v := by rw [hg]; rfl
  · intro hg
    apply LinearMap.ext
    intro v
    apply e.injective
    calc
      e (rho g v) = sigma g (e v) :=
        _root_.Representation.IntertwiningMap.isIntertwining
          (ρ := rho) (σ := sigma) (f := e.toIntertwiningMap) g v
      _ = e v := by rw [hg]; rfl

end RepresentationEquiv

namespace RepresentationKernel

variable {k : Type u} [Field k] {G : Type v} [Group G]
  {V : Type w} [AddCommGroup V] [Module k V]

/-- Coinduction detects trivial action by a normal subgroup contained in the
subgroup from which one coinduces. -/
theorem coind_ker_contains_iff (H A : Subgroup G) [A.Normal]
    (hAH : A ≤ H) (rho : Representation k H V) :
    A ≤ (_root_.Representation.coind H.subtype rho).ker ↔
      A.subgroupOf H ≤ rho.ker := by
  constructor
  · intro hcoind h hh
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    let F : _root_.Representation.coindV H.subtype rho :=
      (InducedCharacterCompatibility.coindVEquivPi H rho).symm
        (fun _ ↦ rho (InducedCharacterCompatibility.cosetFactor H 1)⁻¹ v)
    have hker : (h : G) ∈
        (_root_.Representation.coind H.subtype rho).ker := hcoind hh
    rw [MonoidHom.mem_ker] at hker
    have hact := LinearMap.congr_fun hker F
    have heval := congrArg
      (fun f : _root_.Representation.coindV H.subtype rho ↦ f.1 1) hact
    have hcov := F.property h 1
    change F.1 ((h : G) * 1) = rho h (F.1 1) at hcov
    change F.1 (1 * (h : G)) = F.1 1 at heval
    have hFone : F.1 1 = v := by
      change rho (InducedCharacterCompatibility.cosetFactor H 1)
        (rho (InducedCharacterCompatibility.cosetFactor H 1)⁻¹ v) = v
      exact rho.self_inv_apply _ _
    rw [one_mul] at heval
    rw [mul_one, hFone] at hcov
    calc
      rho h v = F.1 (h : G) := hcov.symm
      _ = F.1 1 := heval
      _ = v := hFone
  · intro hrho g hg
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro F
    apply Subtype.ext
    funext x
    let cH : H :=
      ⟨x * g * x⁻¹,
        hAH ((inferInstance : A.Normal).conj_mem g hg x)⟩
    have hcA : cH ∈ A.subgroupOf H :=
      (inferInstance : A.Normal).conj_mem g hg x
    have htriv : rho cH = 1 := by
      exact (MonoidHom.mem_ker.mp (hrho hcA))
    have hcov := F.property cH x
    change F.1 ((cH : G) * x) = rho cH (F.1 x) at hcov
    have harg : (cH : G) * x = x * g := by
      dsimp only [cH]
      group
    change F.1 (x * g) = F.1 x
    calc
      F.1 (x * g) = F.1 ((cH : G) * x) := congrArg F.1 harg.symm
      _ = rho cH (F.1 x) := hcov
      _ = F.1 x := by rw [htriv]; rfl

end RepresentationKernel

namespace FDRep

variable {k G : Type u} [Field k] [Group G] [Fintype G]

/-- Peterfalvi 1.6(a), in representation form.  A normal subgroup contained
in the inducing subgroup lies in the kernel before induction exactly when it
lies in the kernel after induction. -/
theorem sub_ker_induceFromSubgroup_iff (H A : Subgroup G) [A.Normal]
    (hAH : A ≤ H) (V₀ : FDRep k H) :
    A ≤ (induceFromSubgroup H V₀).ρ.ker ↔
      A.subgroupOf H ≤ V₀.ρ.ker := by
  let V : Rep k H := Rep.of V₀.ρ
  let e :
      (Representation.ind H.subtype V₀.ρ).Equiv
        (Representation.coind H.subtype V₀.ρ) :=
    Representation.equivOfIso (Rep.indCoindIso V)
  have hker :
      (Representation.ind H.subtype V₀.ρ).ker =
        (Representation.coind H.subtype V₀.ρ).ker :=
    RepresentationEquiv.ker_eq e
  change A ≤ (Representation.ind H.subtype V₀.ρ).ker ↔
    A.subgroupOf H ≤ V₀.ρ.ker
  rw [hker]
  exact RepresentationKernel.coind_ker_contains_iff H A hAH V₀.ρ

end FDRep

namespace ClassFunction

variable {k G : Type u} [Field k] [Group G] [Fintype G]

/-- Source `cfInd_irr_eq1`: induction from a normal subgroup takes an
irreducible character to the induction of the trivial character only when
the original character is trivial. -/
theorem induce_irreducible_eq_induce_trivial_iff
    [CharZero k] [IsAlgClosed k]
    (H : Subgroup G) [H.Normal] [Fintype H]
    [Invertible (Nat.card H : k)]
    (chi : IrreducibleCharacter H k) :
    induce H (chi : ClassFunction H k) =
        induce H
          ((IrreducibleCharacter.trivial : IrreducibleCharacter H k) :
            ClassFunction H k) ↔
      chi = IrreducibleCharacter.trivial := by
  constructor
  · intro hind
    have horbit : chi ∈
        MulAction.orbit G (IrreducibleCharacter.trivial :
          IrreducibleCharacter H k) :=
      (cfclass_Ind_irrP H chi IrreducibleCharacter.trivial).2 hind
    rw [MulAction.mem_orbit_iff] at horbit
    obtain ⟨x, hx⟩ := horbit
    calc
      chi = x • (IrreducibleCharacter.trivial :
          IrreducibleCharacter H k) := hx.symm
      _ = IrreducibleCharacter.trivial := by
        apply Subtype.ext
        change ClassFunction.normalConjugate H x
          ((IrreducibleCharacter.trivial : IrreducibleCharacter H k) :
            ClassFunction H k) =
          ((IrreducibleCharacter.trivial : IrreducibleCharacter H k) :
            ClassFunction H k)
        apply ClassFunction.ext
        intro h
        rw [ClassFunction.normalConjugate_apply]
        simp
  · rintro rfl
    rfl

end ClassFunction

end

end Submission.OddOrder.PF
