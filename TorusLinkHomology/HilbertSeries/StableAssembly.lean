import TorusLinkHomology.HilbertSeries.StableFiniteLimit
import TorusLinkHomology.HilbertSeries.StableNormalization
import TorusLinkHomology.HilbertSeries.StabilizationHomology

/-! Assemble stabilization, finite coefficient limits, and the Gordon formula. -/

noncomputable section
namespace TorusLinkHomology.HilbertSeries

/-- The coefficient theorem follows once the actual finite Hilbert series has
been identified with the normalized finite length expression. -/
theorem stable_homology_coefficient_of_normalization (N : ℕ) (hN : 0 < N)
    (hnorm : ∀ n, chargeLengthEquiv (chargeTransform N (hilbertSeries N n)) =
      finiteLengthSeries N n) (k b h n : ℕ) (hn : b < n) :
    (homologyDimension N n (k + N * h) b h : ℚ) =
      MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b)
        (fermionicCoefficient N k) := by
  let m := (N + 1) * k + N + b + 1
  let e : Fin 2 →₀ ℕ := Finsupp.single 0 h + Finsupp.single 1 b
  have he₀ : e 0 = h := by simp [e]
  have he₁ : e 1 = b := by simp [e]
  have hbm : b < m := by dsimp [m]; omega
  have hdim : homologyDimension N n (k + N * h) b h =
      homologyDimension N m (k + N * h) b h := by
    rw [homologyDimension_stable N n _ b h hn,
      homologyDimension_stable N m _ b h hbm]
  rw [hdim]
  change (homologyDimension N m (k + N * h) b h : ℚ) =
    MvPowerSeries.coeff e (fermionicCoefficient N k)
  rw [← he₀, ← he₁, ← coeff_chargeLength_hilbertSeries N m k e, hnorm m,
    coeff_finiteLengthSeries_stable N m k hN e (by dsimp [m]; omega),
    coeff_stableLengthSeries_fermionic N k hN]

/-- The stable coefficient formula, with the finite Hilbert identity as its
only remaining input. All limits are eventual coefficient equalities. -/
theorem stable_homology_coefficient_of_finite (N : ℕ) (hN : 0 < N)
    (hfinite : ∀ n, qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n *
      hilbertSeries N n = finiteNumerator N n) (k b h n : ℕ) (hn : b < n) :
    (homologyDimension N n (k + N * h) b h : ℚ) =
      MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b)
        (fermionicCoefficient N k) :=
  stable_homology_coefficient_of_normalization N hN
    (fun m => chargeLength_hilbertSeries_eq_finiteLengthSeries N m (hfinite m)) k b h n hn

end TorusLinkHomology.HilbertSeries
