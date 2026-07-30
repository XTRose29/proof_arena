import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
Cyclic prime-power automorphisms.

The unit group modulo an odd prime power is cyclic.  The unique subgroup of
order `p` is both the `p`-torsion subgroup and the kernel of reduction by one
power of `p`.  This is the number-theoretic input used in the noncommutative
branch of `BGsection4.v: Ohm1_extremal_odd`.
-/

namespace Submission.OddOrder.MathlibSupport

/-- A `p`-torsion unit modulo `p^(n+2)` is congruent to one modulo
`p^(n+1)`, for odd prime `p`. -/
theorem unitsMap_pow_prime_eq_one
    {p n : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (u : (ZMod (p ^ (n + 2)))ˣ) (hu : u ^ p = 1) :
    ZMod.unitsMap (show p ^ (n + 1) ∣ p ^ (n + 2) by
      exact pow_dvd_pow p (by omega)) u = 1 := by
  let hdiv : p ^ (n + 1) ∣ p ^ (n + 2) := pow_dvd_pow p (by omega)
  letI : NeZero (p ^ (n + 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let U := (ZMod (p ^ (n + 2)))ˣ
  let V := (ZMod (p ^ (n + 1)))ˣ
  let f : U →* V := ZMod.unitsMap hdiv
  letI : IsCyclic U :=
    ZMod.isCyclic_units_of_prime_pow p hp
      (hpodd.ne_two_of_dvd_nat dvd_rfl) (n + 2)
  have hUcard : Nat.card U = p ^ (n + 1) * (p - 1) := by
    dsimp [U]
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    simpa [Nat.add_assoc] using Nat.totient_prime_pow_succ hp (n + 1)
  have hVcard : Nat.card V = p ^ n * (p - 1) := by
    dsimp [V]
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    simpa [Nat.add_assoc] using Nat.totient_prime_pow_succ hp n
  have hfsurj : Function.Surjective f := by
    exact ZMod.unitsMap_surjective hdiv
  have hfindex : f.ker.index = Nat.card V := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hfsurj,
      Subgroup.card_top]
  have hfkerCard : Nat.card f.ker = p := by
    have hprod : Nat.card f.ker * (p ^ n * (p - 1)) =
        p * (p ^ n * (p - 1)) := by
      calc
        Nat.card f.ker * (p ^ n * (p - 1)) =
            Nat.card f.ker * f.ker.index := by rw [hfindex, hVcard]
        _ = Nat.card U := f.ker.card_mul_index
        _ = p * (p ^ n * (p - 1)) := by
          rw [hUcard, pow_succ]
          ac_rfl
    exact Nat.eq_of_mul_eq_mul_right
      (Nat.mul_pos (pow_pos hp.pos n) (Nat.sub_pos_of_lt hp.one_lt)) hprod
  let P : Subgroup U := (powMonoidHom p : U →* U).ker
  have hPcard : Nat.card P = p := by
    dsimp [P]
    rw [IsCyclic.card_powMonoidHom_ker, hUcard]
    apply Nat.gcd_eq_right
    exact dvd_mul_of_dvd_left
      (dvd_pow_self p (by omega : n + 1 ≠ 0)) (p - 1)
  have hker_le : f.ker ≤ P := by
    intro x hx
    change x ^ p = 1
    let xk : f.ker := ⟨x, hx⟩
    have hxk : xk ^ p = 1 := by
      simpa only [hfkerCard] using (pow_card_eq_one' (x := xk))
    exact congrArg Subtype.val hxk
  have hker_eq : f.ker = P :=
    Subgroup.eq_of_le_of_card_ge hker_le (by rw [hPcard, hfkerCard])
  have huP : (u : U) ∈ P := by
    change u ^ p = 1
    exact hu
  have huker : (u : U) ∈ f.ker := hker_eq.symm.le huP
  exact MonoidHom.mem_ker.mp huker

private lemma zmod_nsmul_eq_of_cast_eq
    {p m : ℕ} {a b : ZMod (p * m)}
    (h : (a.cast : ZMod m) = b.cast) :
    p • a = p • b := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective b
  have hab : a ≡ b [ZMOD m] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simpa using h
  have habp : (p : ℤ) * a ≡ (p : ℤ) * b [ZMOD (p * m : ℕ)] := by
    simpa using hab.mul_left' (c := (p : ℤ))
  have heq : (((p : ℤ) * a : ℤ) : ZMod (p * m)) =
      (((p : ℤ) * b : ℤ) : ZMod (p * m)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).2 habp
  simpa [nsmul_eq_mul] using heq

private lemma zmod_nsmul_eq_of_cast_eq'
    {p m N : ℕ} (hN : N = p * m) (hdiv : m ∣ N)
    {a b : ZMod N}
    (h : ZMod.castHom hdiv (ZMod m) a = ZMod.castHom hdiv (ZMod m) b) :
    p • a = p • b := by
  subst N
  exact zmod_nsmul_eq_of_cast_eq h

/-- In the standard cyclic group of order `p^(n+2)`, a `p`-torsion
automorphism fixes every `p`th power. -/
theorem zmod_mulAut_fix_pow_prime
    {p n : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (f : MulAut (Multiplicative (ZMod (p ^ (n + 2)))))
    (hf : f ^ p = 1) (x : Multiplicative (ZMod (p ^ (n + 2)))) :
    f (x ^ p) = x ^ p := by
  let N := p ^ (n + 2)
  let M := p ^ (n + 1)
  let hdiv : M ∣ N := pow_dvd_pow p (by omega)
  let e : MulAut (Multiplicative (ZMod N)) ≃* (ZMod N)ˣ :=
    (MulAutMultiplicative (ZMod N)).trans
      (ZMod.AddAutEquivUnits N).toMultiplicative
  let u : (ZMod N)ˣ := e f
  let a : AddAut (ZMod N) :=
    Multiplicative.toAdd ((MulAutMultiplicative (ZMod N)) f)
  have hu : u ^ p = 1 := by
    dsimp [u]
    rw [← map_pow, hf, map_one]
  have hured : ZMod.unitsMap hdiv u = 1 := by
    exact unitsMap_pow_prime_eq_one hp hpodd u hu
  have hcast : ZMod.castHom hdiv (ZMod M) (u : ZMod N) = 1 := by
    have h := congrArg Units.val hured
    exact h
  have huval : (u : ZMod N) = a 1 := by
    rfl
  have ha (z : ZMod N) : a z = a 1 * z := by
    rw [mul_comm, ← z.intCast_zmod_cast, ← zsmul_eq_mul, ← map_zsmul, zsmul_one]
  rw [map_pow]
  change p • (f x).toAdd = p • x.toAdd
  have hfx : (f x).toAdd = a x.toAdd := by
    rfl
  rw [hfx, ha]
  have hN : N = p * M := by
    dsimp [N, M]
    rw [pow_succ]
    ac_rfl
  have hcasta : ZMod.castHom hdiv (ZMod M) (a 1) = 1 := by
    rw [← huval]
    exact hcast
  apply zmod_nsmul_eq_of_cast_eq'
    (N := N) (m := M) hN (hdiv := hdiv)
  rw [map_mul, hcasta, one_mul]

/-- A `p`-torsion automorphism of a finite cyclic group of order `p^(n+2)`
fixes every `p`th power, when `p` is odd. -/
theorem mulAut_fix_pow_prime_of_pow_eq_one
    {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {p n : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hcard : Nat.card H = p ^ (n + 2))
    (f : MulAut H) (hf : f ^ p = 1) (x : H) :
    f (x ^ p) = x ^ p := by
  let e : Multiplicative (ZMod (p ^ (n + 2))) ≃* H := by
    rw [← hcard]
    exact zmodCyclicMulEquiv (inferInstance : IsCyclic H)
  let g : MulAut (Multiplicative (ZMod (p ^ (n + 2)))) :=
    (MulAut.congr e).symm f
  have hg : g ^ p = 1 := by
    dsimp [g]
    rw [← map_pow, hf, map_one]
  have hfix := zmod_mulAut_fix_pow_prime hp hpodd g hg (e.symm x)
  simpa [g, MulAut.congr] using congrArg e hfix

end Submission.OddOrder.MathlibSupport
