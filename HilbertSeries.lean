import TorusLinkHomology.HilbertSeries.FiniteAssembly
import TorusLinkHomology.HilbertSeries.ReversalSeries
import TorusLinkHomology.HilbertSeries.CoordinateCase
import TorusLinkHomology.HilbertSeries.StabilizationHomology
import TorusLinkHomology.HilbertSeries.StableAssembly

/-! Public algebraic Hilbert-series statements and their corollaries.
Supporting definitions and proofs are in `TorusLinkHomology/HilbertSeries/`.
The finite and stable identities are proved from graded exactness, reversal,
coefficient stabilization, and the Gordon multisum recurrence.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.HilbertSeries

/-- Theorem A.4, algebraic form, including the empty complex n = 0.
Multiplication by (s;v)_n clears the denominator; the right-hand side is a
finite polynomial expression. No rationality assumption on the left is made. -/
theorem finite_hilbert_series (N n : ℕ) (hN : 0 < N) :
    qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n *
      hilbertSeries N n = finiteNumerator N n := by
  exact finite_hilbert_series_proved N n hN

/-- Theorem A.5, algebraic coefficient form.
For weight b, every length n > b already gives the infinite-strand answer.
The coefficient of y^h v^b has polynomial degree a = k + N*h. Thus this
statement includes stabilization and counts the actual finite-stage homology,
rather than defining a putative Hilbert series by the proposed formula. -/
theorem stable_homology_coefficient (N : ℕ) (hN : 0 < N) (k b h n : ℕ)
    (hn : b < n) :
    (homologyDimension N n (k + N * h) b h : ℚ) =
      MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b)
        (fermionicCoefficient N k) := by
  exact stable_homology_coefficient_of_finite N hN
    (fun m => finite_hilbert_series N m hN) k b h n hn

/-- The power-series formulation of Theorem A.5 follows from its coefficient
form, without any additional admission or direct-limit machinery. -/
theorem stable_charge_series (N : ℕ) (hN : 0 < N) (k : ℕ) :
    stableChargeSeries N k = fermionicCoefficient N k := by
  ext e
  have he : Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) = e := by
    ext i
    fin_cases i <;> simp
  simpa only [MvPowerSeries.coeff_apply, stableChargeSeries, he] using
    stable_homology_coefficient N hN k (e 1) (e 0) (e 1 + 1) (Nat.lt_succ_self _)

/-- The integrality and nonnegativity conclusion of Theorem A.5: every
coefficient is a natural-number dimension. -/
theorem fermionicCoefficient_coeff_nat (N : ℕ) (hN : 0 < N) (k : ℕ)
    (e : Fin 2 →₀ ℕ) :
    ∃ d : ℕ, MvPowerSeries.coeff e (fermionicCoefficient N k) = (d : ℚ) := by
  rw [← stable_charge_series N hN k]
  exact ⟨homologyDimension N (e 1 + 1) (k + N * e 0) (e 1) (e 0), rfl⟩

end TorusLinkHomology.HilbertSeries
