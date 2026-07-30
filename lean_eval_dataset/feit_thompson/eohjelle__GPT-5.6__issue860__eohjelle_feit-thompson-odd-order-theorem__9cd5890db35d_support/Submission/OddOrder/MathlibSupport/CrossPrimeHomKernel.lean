import Mathlib.GroupTheory.PGroup

/-!
Trivial kernels forced by incompatible prime-power structures.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G K : Type*} [Group G] [Group K]

/-- A subgroup that is simultaneously p-primary and q-primary for distinct
primes is trivial. -/
theorem eq_bot_of_isPGroup_of_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (H : Subgroup G) (hp : IsPGroup p H) (hq : IsPGroup q H) :
    H = ⊥ := by
  exact disjoint_self.mp
    (IsPGroup.disjoint_of_ne p q hpq H H hp hq)

/-- A homomorphism from a q-group into a p-group has top kernel when the
primes are distinct. -/
theorem ker_eq_top_of_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (f : G →* K)
    (hpq : p ≠ q) (hG : IsPGroup q G) (hK : IsPGroup p K) :
    f.ker = ⊤ := by
  have hRangeQ : IsPGroup q f.range :=
    hG.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hRangeP : IsPGroup p f.range := hK.to_subgroup f.range
  have hRange : f.range = ⊥ :=
    eq_bot_of_isPGroup_of_isPGroup hpq f.range hRangeP hRangeQ
  exact MonoidHom.ker_eq_top_iff.mpr
    (MonoidHom.range_eq_bot_iff.mp hRange)

/-- Every value of a homomorphism from a q-group into a p-group is trivial
for distinct primes. -/
theorem apply_eq_one_of_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (f : G →* K)
    (hpq : p ≠ q) (hG : IsPGroup q G) (hK : IsPGroup p K)
    (g : G) : f g = 1 := by
  exact MonoidHom.mem_ker.mp
    (ker_eq_top_of_isPGroup f hpq hG hK ▸ Subgroup.mem_top g)

end Submission.OddOrder.MathlibSupport
