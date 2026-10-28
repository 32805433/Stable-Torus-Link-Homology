import TorusLinkHomology.HilbertSeries.StableFormula

/-! Normalization of the finite formula in nonnegative charge coordinates. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

private theorem rescale_C' (t c : ChargeSeries) :
    PowerSeries.rescale t (PowerSeries.C c) = PowerSeries.C c := by
  ext k
  cases k <;> simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C]

/-- Clearing the rescaled denominator of the finite ratio. -/
theorem rescale_finiteQBinomialRatioLengths_mul (a t : ChargeSeries) (m n : ℕ) :
    PowerSeries.rescale t (finiteQBinomialRatioLengths a m n) *
      qPochhammer (PowerSeries.X * PowerSeries.C t) (PowerSeries.C (MvPowerSeries.X 1)) n =
    qPochhammer (-PowerSeries.C (a * t) * PowerSeries.X)
      (PowerSeries.C (MvPowerSeries.X 1)) m := by
  have hi := PowerSeries.invOfUnit_mul
    (qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) n) 1
    (constantCoeff_lengthPochhammer (MvPowerSeries.X 1 : ChargeSeries) n)
  have he : finiteQBinomialRatioLengths a m n *
      qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) n =
      qPochhammer (-PowerSeries.C a * PowerSeries.X) (PowerSeries.C (MvPowerSeries.X 1)) m := by
    rw [finiteQBinomialRatioLengths, mul_assoc, hi, mul_one]
  have hh := congrArg (PowerSeries.rescale t) he
  simp only [map_mul, map_qPochhammer, map_neg, PowerSeries.rescale_X, rescale_C'] at hh
  have hnum : -PowerSeries.C a * (PowerSeries.C t * PowerSeries.X) =
      -PowerSeries.C (a * t) * PowerSeries.X := by
    rw [map_mul]
    ring
  rw [hnum, mul_comm (PowerSeries.C t) PowerSeries.X] at hh
  exact hh

/-- The denominator converts one normalized summand into its charged-numerator term. -/
theorem denominator_mul_finiteLengthSummand (N n i j : ℕ) (hi : i ≤ n) :
    qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) n * finiteLengthSummand N n i j =
      (-1 : PowerSeries ChargeSeries) ^ i * PowerSeries.X ^ (N * i) *
        PowerSeries.C (MvPowerSeries.X 1) ^ (quadraticExponent N i + i * j) *
        qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) i *
        qPochhammer (-PowerSeries.C (MvPowerSeries.X 0)) (PowerSeries.C (MvPowerSeries.X 1)) (N * i) *
        chargedCorrection N (PowerSeries.X * PowerSeries.C (MvPowerSeries.X 1) ^ i)
          (PowerSeries.C (MvPowerSeries.X 1))
          (PowerSeries.C (MvPowerSeries.X 0) * PowerSeries.C (MvPowerSeries.X 1) ^ (N * i)) j *
        qPochhammer (-PowerSeries.C (MvPowerSeries.X 0) * PowerSeries.X *
          PowerSeries.C (MvPowerSeries.X 1) ^ ((N + 1) * i + j))
          (PowerSeries.C (MvPowerSeries.X 1)) (n - ((N + 1) * i + j)) *
        gaussianBinomial (PowerSeries.C (MvPowerSeries.X 1)) (n - N * i - j) i := by
  have hd : qPochhammer (PowerSeries.X : PowerSeries ChargeSeries) (PowerSeries.C (MvPowerSeries.X 1)) n =
      qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) i *
        qPochhammer (PowerSeries.X * PowerSeries.C (MvPowerSeries.X 1 ^ i))
          (PowerSeries.C (MvPowerSeries.X 1)) (n - i) := by
    rw [map_pow, ← qPochhammer_add, Nat.add_sub_of_le hi]
  have hp := rescale_finiteQBinomialRatioLengths_mul
    (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i + j)) (MvPowerSeries.X 1 ^ i)
    (n - ((N + 1) * i + j)) (n - i)
  have hexp : N * i + j + i = (N + 1) * i + j := by ring
  have ha : (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i + j)) * MvPowerSeries.X 1 ^ i =
      MvPowerSeries.X 0 * (MvPowerSeries.X 1 : ChargeSeries) ^ ((N + 1) * i + j) := by
    rw [mul_assoc, ← pow_add, hexp]
  rw [ha] at hp
  simp only [finiteLengthSummand, hd]
  simp only [map_mul, map_pow, map_neg, map_one, map_qPochhammer, map_gaussianBinomial] at *
  have harg : -((PowerSeries.C (MvPowerSeries.X 0) : PowerSeries ChargeSeries) * PowerSeries.C (MvPowerSeries.X 1) ^ ((N + 1) * i + j)) *
      PowerSeries.X = -PowerSeries.C (MvPowerSeries.X 0) * PowerSeries.X *
        PowerSeries.C (MvPowerSeries.X 1) ^ ((N + 1) * i + j) := by ring
  rw [harg] at hp
  linear_combination
    ((-1 : PowerSeries ChargeSeries) ^ i * PowerSeries.X ^ (N * i) *
      PowerSeries.C (MvPowerSeries.X 1) ^ (quadraticExponent N i + i * j) *
      qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) i *
      qPochhammer (-PowerSeries.C (MvPowerSeries.X 0)) (PowerSeries.C (MvPowerSeries.X 1)) (N * i) *
      chargedCorrection N (PowerSeries.X * PowerSeries.C (MvPowerSeries.X 1) ^ i)
        (PowerSeries.C (MvPowerSeries.X 1))
        (PowerSeries.C (MvPowerSeries.X 0) * PowerSeries.C (MvPowerSeries.X 1) ^ (N * i)) j *
      gaussianBinomial (PowerSeries.C (MvPowerSeries.X 1)) (n - N * i - j) i) * hp

private theorem chargeLengthEquiv_qPochhammer (a v : Series) (m : ℕ) :
    chargeLengthEquiv (qPochhammer a v m) =
      qPochhammer (chargeLengthEquiv a) (chargeLengthEquiv v) m :=
  map_qPochhammer chargeLengthEquiv.toRingHom a v m

private theorem chargeLengthEquiv_gaussianBinomial (v : Series) (n k : ℕ) :
    chargeLengthEquiv (gaussianBinomial v n k) =
      gaussianBinomial (chargeLengthEquiv v) n k :=
  map_gaussianBinomial chargeLengthEquiv.toRingHom v n k

private theorem chargeLengthEquiv_chargedCorrection (N : ℕ) (s v y : Series) (j : ℕ) :
    chargeLengthEquiv (chargedCorrection N s v y j) =
      chargedCorrection N (chargeLengthEquiv s) (chargeLengthEquiv v) (chargeLengthEquiv y) j :=
  map_chargedCorrection chargeLengthEquiv.toRingHom N s v y j

theorem denominator_mul_finiteLengthSeries (N n : ℕ) :
    qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) n * finiteLengthSeries N n =
      chargeLengthEquiv (chargedFiniteNumerator N n) := by
  classical
  unfold finiteLengthSeries chargedFiniteNumerator
  simp only [Finset.mul_sum, map_sum, apply_ite, map_zero, map_mul, map_pow,
    map_neg, map_one, chargeLengthEquiv_qPochhammer, chargeLengthEquiv_chargedCorrection,
    chargeLengthEquiv_gaussianBinomial,
    chargeLengthEquiv_X_zero, chargeLengthEquiv_X_one, chargeLengthEquiv_X_two]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with hij
  · exact denominator_mul_finiteLengthSummand N n i j (by nlinarith)
  · simp

/-- Normalize the proved finite formula and extract its nonnegative charge
coordinates as an ordinary length series. -/
theorem chargeLength_hilbertSeries_eq_finiteLengthSeries (N n : ℕ)
    (hfinite : qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n *
      hilbertSeries N n = finiteNumerator N n) :
    chargeLengthEquiv (chargeTransform N (hilbertSeries N n)) = finiteLengthSeries N n := by
  have hf := congrArg chargeLengthEquiv (chargedFiniteFormula_of_finite N n hfinite)
  simp only [map_mul, chargeLengthEquiv_qPochhammer, chargeLengthEquiv_X_zero, chargeLengthEquiv_X_one] at hf
  have hunit : IsUnit (qPochhammer (PowerSeries.X : PowerSeries ChargeSeries)
      (PowerSeries.C (MvPowerSeries.X 1)) n) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [constantCoeff_lengthPochhammer]
    exact isUnit_one
  apply hunit.mul_left_cancel
  rw [hf, denominator_mul_finiteLengthSeries]

end TorusLinkHomology.HilbertSeries
