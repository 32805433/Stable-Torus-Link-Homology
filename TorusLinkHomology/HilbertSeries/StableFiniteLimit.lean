import TorusLinkHomology.HilbertSeries.StableFormula

/-! Coefficientwise passage from finite normalized summands to stable ones. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

theorem coeff_length_rescale_of_weight_congr (t : ChargeSeries)
    (f g : PowerSeries ChargeSeries) (n : ℕ)
    (hfg : ∀ m (e : Fin 2 →₀ ℕ), e 1 < n →
      MvPowerSeries.coeff e (PowerSeries.coeff m f) =
        MvPowerSeries.coeff e (PowerSeries.coeff m g))
    (m : ℕ) (e : Fin 2 →₀ ℕ) (he : e 1 < n) :
    MvPowerSeries.coeff e (PowerSeries.coeff m (PowerSeries.rescale t f)) =
      MvPowerSeries.coeff e (PowerSeries.coeff m (PowerSeries.rescale t g)) := by
  simp only [PowerSeries.coeff_rescale]
  exact coeff_mul_of_weight_congr (t ^ m) _ _ n (hfg m) e he

theorem coeff_length_C_mul_of_weight_congr (p : PowerSeries ChargeSeries)
    (f g : ChargeSeries) (n : ℕ)
    (hfg : ∀ e : Fin 2 →₀ ℕ, e 1 < n → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g)
    (m : ℕ) (e : Fin 2 →₀ ℕ) (he : e 1 < n) :
    MvPowerSeries.coeff e (PowerSeries.coeff m (PowerSeries.C f * p)) =
      MvPowerSeries.coeff e (PowerSeries.coeff m (PowerSeries.C g * p)) := by
  simp only [PowerSeries.coeff_C_mul]
  simpa only [mul_comm] using coeff_mul_of_weight_congr (PowerSeries.coeff m p) f g n hfg e he

theorem coeff_finiteLengthSummand_stable (N n i j k : ℕ)
    (e : Fin 2 →₀ ℕ) (h₁ : e 1 < n - ((N + 1) * i + j))
    (h₂ : e 1 < n - i) (h₃ : i + e 1 ≤ n - N * i - j) :
    MvPowerSeries.coeff e (PowerSeries.coeff k (finiteLengthSummand N n i j)) =
      MvPowerSeries.coeff e (PowerSeries.coeff k (stableLengthSummand N i j)) := by
  unfold finiteLengthSummand stableLengthSummand
  calc
    _ = MvPowerSeries.coeff e (PowerSeries.coeff k
        (PowerSeries.C ((-1) ^ i * MvPowerSeries.X 1 ^ (quadraticExponent N i + i * j) *
          qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (N * i) *
          gaussianBinomial (MvPowerSeries.X 1) (n - N * i - j) i) *
        PowerSeries.X ^ (N * i) *
        chargedCorrection N (PowerSeries.X * PowerSeries.C (MvPowerSeries.X 1 ^ i))
          (PowerSeries.C (MvPowerSeries.X 1))
          (PowerSeries.C (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i))) j *
        PowerSeries.rescale (MvPowerSeries.X 1 ^ i)
          (qBinomialRatio (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i + j))))) := by
      apply coeff_length_mul_of_weight_congr _ _ _ (e 1 + 1) ?_ k e (by omega)
      intro m d hd
      apply coeff_length_rescale_of_weight_congr _ _ _ (e 1 + 1) ?_ m d hd
      intro l c hc
      exact coeff_finiteQBinomialRatioLengths_stable _ _ _ l c (by omega) (by omega)
    _ = _ := by
      simp only [mul_assoc]
      apply coeff_length_C_mul_of_weight_congr _ _ _ (e 1 + 1) ?_ k e (by omega)
      intro d hd
      convert coeff_mul_gaussianBinomial_stable
        ((-1) ^ i * MvPowerSeries.X 1 ^ (quadraticExponent N i + i * j) *
          qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (N * i))
        (n - N * i - j) i d (by omega) using 1 <;> congr 1 <;> ring

theorem coeff_finiteLengthSummand_eq_zero (N n i j k : ℕ) (hi : k < N * i) :
    PowerSeries.coeff k (finiteLengthSummand N n i j) = 0 := by
  unfold finiteLengthSummand
  rw [show ∀ (a b c : PowerSeries ChargeSeries), a * PowerSeries.X ^ (N * i) * b * c =
      PowerSeries.X ^ (N * i) * (a * b * c) by intros; ring]
  rw [PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hi]

theorem coeff_stableLengthSummand_eq_zero (N i j k : ℕ) (hi : k < N * i) :
    PowerSeries.coeff k (stableLengthSummand N i j) = 0 := by
  unfold stableLengthSummand
  rw [show ∀ (a b c : PowerSeries ChargeSeries), a * PowerSeries.X ^ (N * i) * b * c =
      PowerSeries.X ^ (N * i) * (a * b * c) by intros; ring]
  rw [PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hi]

/-- At a fixed charge and weight a single explicit finite length suffices for
all the Gaussian factors and product ratios in the finite sum. -/
theorem coeff_finiteLengthSeries_stable (N n k : ℕ) (hN : 0 < N)
    (e : Fin 2 →₀ ℕ) (hn : (N + 1) * k + N + e 1 + 1 ≤ n) :
    MvPowerSeries.coeff e (PowerSeries.coeff k (finiteLengthSeries N n)) =
      MvPowerSeries.coeff e (PowerSeries.coeff k (stableLengthSeries N k)) := by
  have hkn : k ≤ n := by nlinarith
  unfold finiteLengthSeries stableLengthSeries
  simp only [map_sum]
  rw [← Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hkn 1))]
  · apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    apply Finset.sum_congr rfl
    intro j hj
    have hjN : j ≤ N := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    have hbound : (N + 1) * i + j + e 1 + 1 ≤ n := by nlinarith
    rw [if_pos (by omega)]
    apply coeff_finiteLengthSummand_stable
    · omega
    · have hii : i ≤ (N + 1) * i := by nlinarith
      omega
    · have heq : (N + 1) * i = N * i + i := by ring
      omega
  · intro i hi hin
    have hik : k < i := by
      simp only [Finset.mem_range] at hin
      omega
    apply Finset.sum_eq_zero
    intro j hj
    split_ifs
    · rw [coeff_finiteLengthSummand_eq_zero N n i j k (by nlinarith), map_zero]
    · simp

end TorusLinkHomology.HilbertSeries
