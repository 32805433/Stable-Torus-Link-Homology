import TorusLinkHomology.HilbertSeries.FiniteRecurrence
import TorusLinkHomology.HilbertSeries.CoordinateCase

/-! The finite Hilbert identity for the coordinate Koszul complex (N=1). -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

@[simp] theorem hilbertSeries_one (n : ℕ) : hilbertSeries 1 n = 1 := by
  classical
  ext e
  have he : e = 0 ↔ e 0 = 0 ∧ e 1 = 0 ∧ e 2 = 0 := by
    constructor
    · rintro rfl; simp
    · rintro ⟨h0, h1, h2⟩
      ext i
      fin_cases i <;> assumption
  rw [MvPowerSeries.coeff_one]
  change (homologyDimension 1 n (e 0) (e 1) (e 2) : ℚ) = _
  simp [homologyDimension_one, he]

theorem finiteNumeratorAt_rank_one {S : Type*} [CommRing S] (n : ℕ) (s v z : S) :
    finiteNumeratorAt 1 n s v z = qPochhammer s v n := by
  classical
  induction n using Nat.strong_induction_on generalizing s v z with
  | h n ih =>
    cases n with
    | zero => simp [finiteNumeratorAt, finiteTerm, finiteWeight, Finset.sum_range_succ,
        quadraticExponent, numeratorCorrection]
    | succ n =>
      cases n with
      | zero =>
        simp [finiteNumeratorAt, finiteTerm, finiteWeight, Finset.sum_range_succ,
          quadraticExponent, numeratorCorrection, gaussianBinomial]
        ring
      | succ n =>
        rw [finiteNumeratorAt_recurrence 1 (n + 1) (by omega),
          ih (n + 1) (by omega), ih ((n + 1) - 1) (by omega)]
        simp only [Nat.add_sub_cancel, pow_one]
        rw [qPochhammer_succ s v (n + 1), qPochhammer_shift s v n]
        simp only [qPochhammer_one]
        ring

@[simp] theorem finiteNumerator_rank_one (n : ℕ) :
    finiteNumerator 1 n = qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n := by
  rw [finiteNumerator_eq_at, finiteNumeratorAt_rank_one]

/-- The finite formula for N=1 at every length, including zero. -/
theorem finite_hilbert_series_one (n : ℕ) :
    qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n *
      hilbertSeries 1 n = finiteNumerator 1 n := by simp

end TorusLinkHomology.HilbertSeries
