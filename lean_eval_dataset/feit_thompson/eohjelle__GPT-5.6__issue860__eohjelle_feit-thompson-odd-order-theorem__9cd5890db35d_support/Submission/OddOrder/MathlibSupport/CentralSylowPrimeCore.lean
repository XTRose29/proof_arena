import Mathlib.GroupTheory.Transfer
import Submission.OddOrder.MathlibSupport.PPrimeCore

/-!
The `p'`-core complements a central Sylow subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A Sylow subgroup contained in the center has the `p'`-core as a normal
complement. This is the Burnside-transfer input in Bender-Glauberman
Proposition 4.4(b). -/
theorem pPrimeCore_isComplement_centralSylow
    (P : Sylow p G) (hPcenter : (P : Subgroup G) ≤ Subgroup.center G) :
    (pPrimeCore p G).IsComplement' (P : Subgroup G) := by
  have hnormCent : Subgroup.normalizer (P : Set G) ≤
      Subgroup.centralizer (P : Set G) := by
    intro g _ x hx
    exact (Subgroup.mem_center_iff.mp (hPcenter hx) g).symm
  let K : Subgroup G := (MonoidHom.transferSylow P hnormCent).ker
  have hKcomp : K.IsComplement' (P : Subgroup G) :=
    MonoidHom.ker_transferSylow_isComplement' P hnormCent
  have hKprime : IsPPrimeSubgroup p K := by
    rw [IsPPrimeSubgroup]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (MonoidHom.not_dvd_card_ker_transferSylow P hnormCent)
  have hKle : K ≤ pPrimeCore p G :=
    le_pPrimeCore hKprime (by dsimp [K]; infer_instance)
  have hcoreLe : pPrimeCore p G ≤ K := by
    let q : G →* G ⧸ K := QuotientGroup.mk' K
    have hquotP : IsPGroup p (G ⧸ K) := by
      let e : (G ⧸ K) ≃* P := hKcomp.symm.QuotientMulEquiv
      exact P.isPGroup'.of_equiv e.symm
    let Obar : Subgroup (G ⧸ K) := (pPrimeCore p G).map q
    have hObarP : IsPGroup p Obar := hquotP.to_subgroup Obar
    have hObarPrime : Nat.Coprime p (Nat.card Obar) :=
      (pPrimeCore_coprime_card (G := G) (p := p)).coprime_dvd_right
        (Subgroup.card_map_dvd (pPrimeCore p G) q)
    have hObarCard : Nat.card Obar = 1 :=
      hObarP.card_eq_or_dvd.resolve_right
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hObarPrime)
    have hObarBot : Obar = ⊥ := Subgroup.card_eq_one.mp hObarCard
    have hker : pPrimeCore p G ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (pPrimeCore p G)).mp hObarBot
    simpa [q, QuotientGroup.ker_mk'] using hker
  have hK : K = pPrimeCore p G := le_antisymm hKle hcoreLe
  simpa [hK] using hKcomp

end Submission.OddOrder.MathlibSupport
