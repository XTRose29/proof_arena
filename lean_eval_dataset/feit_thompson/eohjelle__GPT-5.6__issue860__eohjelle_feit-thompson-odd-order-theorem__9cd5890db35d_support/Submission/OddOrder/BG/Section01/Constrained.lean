import Submission.OddOrder.MathlibSupport.FittingPCore
import Submission.OddOrder.MathlibSupport.PPrimePCore

/-!
The `p`-constrained predicate from `BGsection1`.

Sylow subgroups of `O_{p',p}(G)` are subgroups of that subgroup type.  The
small `sylowInAmbient` wrapper maps them back into `G`, where centralizers are
taken in the source statement.
-/

namespace Submission.OddOrder.BG.Section01

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- A Sylow subgroup of `K`, regarded as a subgroup of the ambient group. -/
def sylowInAmbient {p : ℕ} {K : Subgroup G} (P : Sylow p K) : Subgroup G :=
  (P : Subgroup K).map K.subtype

theorem sylowInAmbient_le {p : ℕ} {K : Subgroup G} (P : Sylow p K) :
    sylowInAmbient P ≤ K := by
  exact Subgroup.map_subtype_le _

theorem sylowInAmbient_isPGroup {p : ℕ} {K : Subgroup G} (P : Sylow p K) :
    IsPGroup p (sylowInAmbient P) :=
  P.isPGroup'.map K.subtype

/-- Bender-Glauberman `p`-constrainedness. -/
def IsPConstrained (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ P : Sylow p (pPrimePCore p G),
    Subgroup.centralizer (sylowInAmbient P : Set G) ≤ pPrimePCore p G

theorem isPConstrained_of_pPrimeCore_eq_bot [Finite G] {p : ℕ}
    [Fact p.Prime] [IsSolvable G] (hprimeCore : pPrimeCore p G = ⊥) :
    IsPConstrained p G := by
  intro P
  have hK : pPrimePCore p G = pCore p G := by
    exact pPrimePCore_eq_pCore_of_pPrimeCore_eq_bot hprimeCore
  have hKp : IsPGroup p (pPrimePCore p G) := by
    rw [hK]
    exact pCore_isPGroup
  have hPtop : (P : Subgroup (pPrimePCore p G)) = ⊤ := by
    exact (P.is_maximal' (hKp.to_subgroup ⊤) le_top).symm
  have hPambient : sylowInAmbient P = pPrimePCore p G := by
    rw [sylowInAmbient, hPtop]
    calc
      (⊤ : Subgroup (pPrimePCore p G)).map (pPrimePCore p G).subtype =
          (pPrimePCore p G).subtype.range :=
        (MonoidHom.range_eq_map (pPrimePCore p G).subtype).symm
      _ = pPrimePCore p G := (pPrimePCore p G).range_subtype
  rw [hPambient, hK]
  exact centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot hprimeCore

end Submission.OddOrder.BG.Section01
