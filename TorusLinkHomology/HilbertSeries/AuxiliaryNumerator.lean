import TorusLinkHomology.HilbertSeries.AuxiliaryDimensions
import TorusLinkHomology.HilbertSeries.QSeries.SpecializationApplications

/-! Clearing the passive factors in the auxiliary Hilbert recurrence. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- Denominator of the polynomial ring with weights 1,...,r. -/
def auxiliaryDenominator (r : ℕ) : ChargeSeries :=
  qPochhammer (MvPowerSeries.X 0) (MvPowerSeries.X 0) r

/-- Contribution of the exterior generators with zero differential in reversal. -/
def passiveExteriorProduct (N r m : ℕ) : ChargeSeries :=
  qPochhammer (-MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ (N * r + 1))
    (MvPowerSeries.X 0) (r - m)

/-- The normalized original Hilbert series at positive auxiliary weights. -/
def specializedHilbertNumerator (N n C r : ℕ) : ChargeSeries :=
  positiveSpecialization C r
    (qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n * hilbertSeries N n)

theorem auxiliaryDenominator_succ (r : ℕ) :
    auxiliaryDenominator (r + 1) =
      (1 - (MvPowerSeries.X 0 : ChargeSeries) ^ (r + 1)) * auxiliaryDenominator r := by
  rw [auxiliaryDenominator, qPochhammer_succ]
  simp only [pow_succ, auxiliaryDenominator]
  ring

theorem passiveExteriorProduct_step (N r n : ℕ) (hn : n ≤ r) :
    passiveExteriorProduct N (r + 1) n =
      passiveExteriorProduct N (r + 1) (n + 1) *
        (1 + (MvPowerSeries.X 1 : ChargeSeries) *
          MvPowerSeries.X 0 ^ ((N + 1) * (r + 1) - n)) := by
  have hl : r + 1 - n = (r - n) + 1 := by omega
  have he : N * (r + 1) + 1 + (r - n) = (N + 1) * (r + 1) - n := by
    rw [Nat.add_mul, one_mul]
    omega
  simp only [passiveExteriorProduct, Nat.add_sub_add_right, hl, qPochhammer_succ,
    neg_mul, sub_neg_eq_add, mul_assoc, ← pow_add, he]

theorem passiveExteriorProduct_rank_step (N r n : ℕ) (hNn : N ≤ n) (hn : n ≤ r) :
    passiveExteriorProduct N r (n - N) =
      qPochhammer (-MvPowerSeries.X 1 * (MvPowerSeries.X 0 : ChargeSeries) ^ (N * r + 1))
        (MvPowerSeries.X 0) N * passiveExteriorProduct N (r + 1) (n + 1) := by
  have hl : r - (n - N) = N + (r - n) := by omega
  have he : N * r + 1 + N = N * (r + 1) + 1 := by ring
  simp only [passiveExteriorProduct, hl, qPochhammer_add, Nat.add_sub_add_right,
    mul_assoc, ← pow_add, he]

theorem passiveExteriorProduct_isUnit (N r m : ℕ) : IsUnit (passiveExteriorProduct N r m) := by
  apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
  rw [passiveExteriorProduct, constantCoeff_qPochhammer _ _ (by simp)]
  exact isUnit_one

/-- The auxiliary exact sequence at the offset used for the length recurrence. -/
theorem auxiliary_recurrence_at_reversal (N n r : ℕ) (hN : 0 < N)
    (hNn : N ≤ n) (hn : n ≤ r) :
    Auxiliary.hilbertSeries N (r + 1) (N * (r + 1) - n) =
      Auxiliary.hilbertSeries N (r + 1) (N * (r + 1) - (n + 1)) +
        (MvPowerSeries.X 0 : ChargeSeries) ^ (N * (r + 1) - n) *
          Auxiliary.hilbertSeries N r (N * r - (n - N)) := by
  have hnr : n < N * (r + 1) := by
    have := Nat.mul_le_mul_right (r + 1) hN
    omega
  have hlen : N * (r + 1) - (n + 1) + 1 = N * (r + 1) - n := by omega
  have hoff : N * r - (n - N) = N * (r + 1) - n := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have he := Auxiliary.hilbertSeries_recurrence N (N * (r + 1) - (n + 1)) r hN
    (by omega)
  simpa only [hlen, hoff] using he

/-- A generic cancellation form of the auxiliary recurrence. The only hypotheses
about homology are the auxiliary recurrence and the three reversal identities. -/
theorem specialized_recurrence_of_reversal (N n r C : ℕ) (hNn : N ≤ n) (hn : n ≤ r)
    (haux : Auxiliary.hilbertSeries N (r + 1) (N * (r + 1) - n) =
      Auxiliary.hilbertSeries N (r + 1) (N * (r + 1) - (n + 1)) +
        (MvPowerSeries.X 0 : ChargeSeries) ^ (N * (r + 1) - n) *
          Auxiliary.hilbertSeries N r (N * r - (n - N)))
    (hrev : auxiliaryDenominator (r + 1) *
        Auxiliary.hilbertSeries N (r + 1) (N * (r + 1) - n) =
      passiveExteriorProduct N (r + 1) n * specializedHilbertNumerator N n C (r + 1))
    (hrevNext : auxiliaryDenominator (r + 1) *
        Auxiliary.hilbertSeries N (r + 1) (N * (r + 1) - (n + 1)) =
      passiveExteriorProduct N (r + 1) (n + 1) * specializedHilbertNumerator N (n + 1) C (r + 1))
    (hrevLower : auxiliaryDenominator r *
        Auxiliary.hilbertSeries N r (N * r - (n - N)) =
      passiveExteriorProduct N r (n - N) * specializedHilbertNumerator N (n - N) C r) :
    specializedHilbertNumerator N (n + 1) C (r + 1) =
      (1 + (MvPowerSeries.X 1 : ChargeSeries) *
        MvPowerSeries.X 0 ^ ((N + 1) * (r + 1) - n)) * specializedHilbertNumerator N n C (r + 1) -
      (1 - MvPowerSeries.X 0 ^ (r + 1)) * MvPowerSeries.X 0 ^ (N * (r + 1) - n) *
        qPochhammer (-MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ (N * r + 1))
          (MvPowerSeries.X 0) N * specializedHilbertNumerator N (n - N) C r := by
  have he := congrArg (fun x => auxiliaryDenominator (r + 1) * x) haux
  rw [hrev, mul_add, hrevNext] at he
  have hl : auxiliaryDenominator (r + 1) *
      (MvPowerSeries.X 0 ^ (N * (r + 1) - n) * Auxiliary.hilbertSeries N r (N * r - (n - N))) =
      (1 - (MvPowerSeries.X 0 : ChargeSeries) ^ (r + 1)) *
        MvPowerSeries.X 0 ^ (N * (r + 1) - n) *
        (passiveExteriorProduct N r (n - N) * specializedHilbertNumerator N (n - N) C r) := by
    rw [auxiliaryDenominator_succ, ← hrevLower]
    ring
  rw [hl, passiveExteriorProduct_step N r n hn,
    passiveExteriorProduct_rank_step N r n hNn hn] at he
  apply (passiveExteriorProduct_isUnit N (r + 1) (n + 1)).mul_left_cancel
  linear_combination -he

end TorusLinkHomology.HilbertSeries
