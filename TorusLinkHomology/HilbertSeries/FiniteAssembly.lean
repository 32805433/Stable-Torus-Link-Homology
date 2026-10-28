import TorusLinkHomology.HilbertSeries.FiniteFormula
import TorusLinkHomology.HilbertSeries.FiniteSpecialization
import TorusLinkHomology.HilbertSeries.AuxiliaryNumerator
import TorusLinkHomology.HilbertSeries.ReversalSeries

/-! Final finite-formula assembly from the cleared general reversal identity. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- All remaining finite-formula work is reduced to the graded general reversal
identity. The initial identities, comparison recurrence, polynomial recurrence,
and coefficient separation are proved independently of this premise. -/
theorem finite_hilbert_series_of_reversal (N : ℕ) (hN : 0 < N)
    (hrev : ∀ r m C : ℕ, m ≤ r → m - 1 ≤ C → C < r →
      auxiliaryDenominator r * Auxiliary.hilbertSeries N r (N * r - m) =
        passiveExteriorProduct N r m * specializedHilbertNumerator N m C r)
    (n : ℕ) :
    qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n *
      hilbertSeries N n = finiteNumerator N n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact finite_hilbert_series_empty N
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    by_cases hmN : m ≤ N
    · exact finite_hilbert_series_shortRange N m hN hmN
    have hNm : N ≤ m := by omega
    apply eq_of_positiveSpecialization_eq m
      (coneSupported_hilbertNumerator N (m + 1) m hN (by omega))
      ((coneSupported_finiteNumerator N (m + 1) hN).mono (by omega))
    refine ⟨m + 2, ?_⟩
    intro rho hrho
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rho ≠ 0)
    have hr : m < r := by omega
    have hm : m ≤ r := by omega
    have hactual := specialized_recurrence_of_reversal N m r m hNm hm
      (auxiliary_recurrence_at_reversal N m r hN hNm hm)
      (hrev (r + 1) m m (by omega) (by omega) (by omega))
      (hrev (r + 1) (m + 1) m (by omega) (by omega) (by omega))
      (hrev r (m - N) m (by omega) (by omega) hr)
    have hmFormula := ih m (by omega)
    have hlowerFormula := ih (m - N) (by omega)
    simp only [specializedHilbertNumerator, hmFormula, hlowerFormula] at hactual
    exact hactual.trans
      (positiveSpecialization_finiteNumerator_recurrence_succ N m m r hN hNm le_rfl hr).symm

/-- The finite formula, assembled from the actual graded homology and the
explicit numerator recurrence. -/
theorem finite_hilbert_series_proved (N n : ℕ) (hN : 0 < N) :
    qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n *
      hilbertSeries N n = finiteNumerator N n := by
  apply finite_hilbert_series_of_reversal N hN
  intro r m C hmr hm hr
  exact GeneralReversal.cleared_reversal N r m C hN hmr hm hr

end TorusLinkHomology.HilbertSeries
