import TorusLinkHomology.HilbertSeries.ChargedFiniteFormula
import TorusLinkHomology.HilbertSeries.StableAlternating
import TorusLinkHomology.HilbertSeries.QSeries.StableProducts
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! Extraction of fixed charge from the finite Hilbert formula. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- Regard a charged three-variable series as a series in s with coefficients
in (y,v), keeping the established ChargeSeries coordinate order. -/
def chargeLengthEquiv : Series ≃ₐ[ℚ] PowerSeries ChargeSeries :=
  (MvPowerSeries.renameEquiv ℚ (Equiv.swap (1 : Fin 3) 2)).trans
    (MvPowerSeries.finSuccEquiv ℚ 2)

@[simp] theorem chargeLengthEquiv_X_zero :
    chargeLengthEquiv (MvPowerSeries.X 0) = PowerSeries.X := by
  change MvPowerSeries.finSuccEquiv ℚ 2
    (MvPowerSeries.rename (Equiv.swap (1 : Fin 3) 2) (MvPowerSeries.X 0)) = _
  rw [MvPowerSeries.rename_X]
  simp [Equiv.swap_apply_def]

@[simp] theorem chargeLengthEquiv_X_one :
    chargeLengthEquiv (MvPowerSeries.X 1) = PowerSeries.C (MvPowerSeries.X 1) := by
  change MvPowerSeries.finSuccEquiv ℚ 2
    (MvPowerSeries.rename (Equiv.swap (1 : Fin 3) 2) (MvPowerSeries.X 1)) = _
  rw [MvPowerSeries.rename_X]
  simpa using MvPowerSeries.finSuccEquiv_X_succ (R := ℚ) (n := 2) (1 : Fin 2)

@[simp] theorem chargeLengthEquiv_X_two :
    chargeLengthEquiv (MvPowerSeries.X 2) = PowerSeries.C (MvPowerSeries.X 0) := by
  change MvPowerSeries.finSuccEquiv ℚ 2
    (MvPowerSeries.rename (Equiv.swap (1 : Fin 3) 2) (MvPowerSeries.X 2)) = _
  rw [MvPowerSeries.rename_X]
  simpa using MvPowerSeries.finSuccEquiv_X_succ (R := ℚ) (n := 2) (0 : Fin 2)

theorem coeff_chargeLengthEquiv (f : Series) (k : ℕ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.coeff k (chargeLengthEquiv f)) =
      MvPowerSeries.coeff (tridegree k (e 1) (e 0)) f := by
  change MvPowerSeries.coeff e (PowerSeries.coeff k
    (MvPowerSeries.finSuccEquiv ℚ 2
      (MvPowerSeries.rename (Equiv.swap (1 : Fin 3) 2) f))) = _
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv]
  have he : e.cons k = Finsupp.embDomain (Equiv.swap (1 : Fin 3) 2).toEmbedding
      (tridegree k (e 1) (e 0)) := by
    ext i
    fin_cases i
    · simp [tridegree, Finsupp.embDomain_eq_mapDomain, Equiv.swap_apply_def]
    · change e 0 = _
      simp [tridegree, Finsupp.embDomain_eq_mapDomain]
    · change e 1 = _
      simp [tridegree, Finsupp.embDomain_eq_mapDomain]
  rw [he]
  exact MvPowerSeries.coeff_embDomain_rename
    (Equiv.swap (1 : Fin 3) 2).toEmbedding f (tridegree k (e 1) (e 0))

/-- Coefficients of the charge-length transform are the actual homogeneous
homology dimensions, before any finite or stable formula is invoked. -/
theorem coeff_chargeLength_hilbertSeries (N n k : ℕ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
      (PowerSeries.coeff k (chargeLengthEquiv (chargeTransform N (hilbertSeries N n)))) =
      (homologyDimension N n (k + N * e 0) (e 1) (e 0) : ℚ) := by
  rw [coeff_chargeLengthEquiv, coeff_chargeTransform]
  simp [MvPowerSeries.coeff_apply, hilbertSeries, chargeDegree]

/-- A normalized summand after the Gaussian factor and both product lengths
have reached their coefficientwise limits. -/
def stableLengthSummand (N i j : ℕ) : PowerSeries ChargeSeries :=
  PowerSeries.C ((-1) ^ i * MvPowerSeries.X 1 ^ (quadraticExponent N i + i * j) *
      qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (N * i) * gordonDenominator i) *
    PowerSeries.X ^ (N * i) *
    chargedCorrection N (PowerSeries.X * PowerSeries.C (MvPowerSeries.X 1 ^ i))
      (PowerSeries.C (MvPowerSeries.X 1))
      (PowerSeries.C (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i))) j *
    PowerSeries.rescale (MvPowerSeries.X 1 ^ i)
      (qBinomialRatio (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i + j)))

/-- The finite normalized summand with the two actual truncation lengths. -/
def finiteLengthSummand (N n i j : ℕ) : PowerSeries ChargeSeries :=
  PowerSeries.C ((-1) ^ i * MvPowerSeries.X 1 ^ (quadraticExponent N i + i * j) *
      qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (N * i) *
      gaussianBinomial (MvPowerSeries.X 1) (n - N * i - j) i) *
    PowerSeries.X ^ (N * i) *
    chargedCorrection N (PowerSeries.X * PowerSeries.C (MvPowerSeries.X 1 ^ i))
      (PowerSeries.C (MvPowerSeries.X 1))
      (PowerSeries.C (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i))) j *
    PowerSeries.rescale (MvPowerSeries.X 1 ^ i)
      (finiteQBinomialRatioLengths (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i + j))
        (n - ((N + 1) * i + j)) (n - i))

def finiteLengthSeries (N n : ℕ) : PowerSeries ChargeSeries :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (N + 1),
    if (N + 1) * i + j ≤ n then finiteLengthSummand N n i j else 0

def stableLengthSeries (N k : ℕ) : PowerSeries ChargeSeries :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (N + 1), stableLengthSummand N i j

theorem coeff_C_X_pow_rescale_qBinomial (c a : ChargeSeries) (r t k : ℕ) :
    PowerSeries.coeff k (PowerSeries.C c * PowerSeries.X ^ r *
      PowerSeries.rescale (MvPowerSeries.X 1 ^ t) (qBinomialRatio a)) =
      if r ≤ k then c * MvPowerSeries.X 1 ^ (t * (k - r)) *
        qPochhammer (-a) (MvPowerSeries.X 1) (k - r) * gordonDenominator (k - r) else 0 := by
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  split_ifs with hr
  · rw [PowerSeries.coeff_rescale, coeff_qBinomialRatio, ← pow_mul]
    ring
  · simp

theorem coeff_stableLengthSummand_zero (N i k : ℕ) :
    PowerSeries.coeff k (stableLengthSummand N i 0) = stableChargeFirst N k i := by
  simp only [stableLengthSummand, chargedCorrection, Nat.mul_zero, add_zero, mul_one]
  rw [coeff_C_X_pow_rescale_qBinomial]
  unfold stableChargeFirst
  split_ifs with hi
  · have hp : qPochhammer (-MvPowerSeries.X 0 : ChargeSeries) (MvPowerSeries.X 1) k =
        qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (N * i) *
          qPochhammer (-(MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i)))
            (MvPowerSeries.X 1) (k - N * i) := by
      rw [← neg_mul, ← qPochhammer_add, Nat.add_sub_of_le hi]
    rw [hp, pow_add]
    ring
  · rfl

private theorem chargedCorrection_one_split (c t v y : ChargeSeries) (r N : ℕ)
    (f : PowerSeries ChargeSeries) :
    PowerSeries.C c * PowerSeries.X ^ r *
        chargedCorrection N (PowerSeries.X * PowerSeries.C t) (PowerSeries.C v) (PowerSeries.C y) 1 * f =
      -(PowerSeries.C (c * t ^ N) * PowerSeries.X ^ (r + N) * f) -
        (PowerSeries.C (c * y * t) * PowerSeries.X ^ (r + 1) * f) := by
  simp only [chargedCorrection, map_mul, map_pow, mul_pow, pow_add, pow_one]
  ring

theorem coeff_stableLengthSummand_one (N i k : ℕ) :
    PowerSeries.coeff k (stableLengthSummand N i 1) =
      -stableChargeSecond N k i - stableChargeThird N k i := by
  unfold stableLengthSummand
  rw [chargedCorrection_one_split, map_sub, map_neg,
    coeff_C_X_pow_rescale_qBinomial, coeff_C_X_pow_rescale_qBinomial]
  simp only [Nat.mul_one]
  unfold stableChargeSecond stableChargeThird
  simp only [Nat.sub_sub]
  split_ifs <;> simp only [pow_add, pow_mul, Nat.mul_add, Nat.mul_one] <;> ring_nf

private theorem shifted_qBinomial_parameter (a t : ChargeSeries) :
    (1 - PowerSeries.X * PowerSeries.C t) *
      PowerSeries.rescale t (qBinomialRatio (a * MvPowerSeries.X 1)) =
      PowerSeries.rescale (MvPowerSeries.X 1 * t) (qBinomialRatio a) := by
  have he := congrArg (PowerSeries.rescale t) (qBinomialRatio_parameter_shift a)
  simpa only [map_mul, map_sub, map_one, PowerSeries.rescale_X,
    PowerSeries.rescale_rescale, mul_comm] using he

private theorem chargedCorrection_higher_split (c t v y a : ChargeSeries) (r N j : ℕ) :
    PowerSeries.C c * PowerSeries.X ^ r *
        chargedCorrection N (PowerSeries.X * PowerSeries.C t) (PowerSeries.C v)
          (PowerSeries.C y) (j + 2) * PowerSeries.rescale t (qBinomialRatio a) =
      -(PowerSeries.C (c * t ^ N * v ^ (j + 1) * qPochhammer (-y) v (j + 1)) *
        PowerSeries.X ^ (r + N) *
        ((1 - PowerSeries.X * PowerSeries.C t) * PowerSeries.rescale t (qBinomialRatio a))) := by
  simp only [chargedCorrection, map_mul, map_pow, map_qPochhammer, map_neg,
    mul_pow, pow_add]
  ring

theorem coeff_stableLengthSummand_higher (N i j k : ℕ) :
    PowerSeries.coeff k (stableLengthSummand N i (j + 2)) =
      -stableChargeFourth N k i (j + 2) := by
  unfold stableLengthSummand
  rw [chargedCorrection_higher_split]
  have ha : (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i + (j + 2)) : ChargeSeries) =
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i + j + 1)) * MvPowerSeries.X 1 := by
    have he : N * i + (j + 2) = (N * i + j + 1) + 1 := by omega
    rw [he, pow_succ]
    ring
  rw [ha, shifted_qBinomial_parameter, ← pow_succ', map_neg,
    coeff_C_X_pow_rescale_qBinomial]
  unfold stableChargeFourth
  split_ifs with hni
  · have hprod : qPochhammer (-MvPowerSeries.X 0 : ChargeSeries) (MvPowerSeries.X 1) (N * i) *
        qPochhammer (-(MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i)))
          (MvPowerSeries.X 1) (j + 1) =
        qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (N * i + j + 1) := by
      rw [← neg_mul, ← qPochhammer_add]
      congr 1
    have hp : qPochhammer (-MvPowerSeries.X 0 : ChargeSeries) (MvPowerSeries.X 1)
        (N * i + (k - N * i - N) + (j + 2) - 1) =
        qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (N * i + j + 1) *
          qPochhammer (-(MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i + j + 1)))
            (MvPowerSeries.X 1) (k - (N * i + N)) := by
      rw [← neg_mul, ← qPochhammer_add]
      congr 1
      omega
    have he : quadraticExponent N i + i * (k - N * i - N + N + (j + 2)) +
        (k - N * i - N) + (j + 2) - 1 =
        quadraticExponent N i + i * (j + 2) + i * N + (j + 1) +
          (i + 1) * (k - (N * i + N)) := by
      have hr : k - N * i - N = k - (N * i + N) := by omega
      rw [hr]
      have hb : 1 ≤ quadraticExponent N i + i * (k - (N * i + N) + N + (j + 2)) +
          (k - (N * i + N)) + (j + 2) := by omega
      have hh := Nat.sub_add_cancel hb
      nlinarith
    rw [hp, he]
    simp only [pow_add, pow_mul, Nat.sub_sub]
    have hm := congrArg (fun x : ChargeSeries => -( (-1 : ChargeSeries) ^ i *
      (MvPowerSeries.X 1) ^ (quadraticExponent N i + i * (j + 2) + i * N + (j + 1) +
        (i + 1) * (k - (N * i + N))) * gordonDenominator i *
      qPochhammer (-(MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * i + j + 1)))
        (MvPowerSeries.X 1) (k - (N * i + N)) *
      gordonDenominator (k - (N * i + N))) * x) hprod
    simp only [pow_add, pow_mul] at hm
    linear_combination hm
  · simp

/-- Extracting charge k from the stable normalized summands gives exactly
the four finite sums of the draft's alternating charge formula. -/
theorem coeff_stableLengthSeries (N k : ℕ) (hN : 0 < N) :
    PowerSeries.coeff k (stableLengthSeries N k) = stableAlternatingCharge N k := by
  unfold stableLengthSeries stableAlternatingCharge
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  have hhigher : (∑ j ∈ Finset.Ico 2 (N + 1),
      PowerSeries.coeff k (stableLengthSummand N i j)) =
      -(∑ j ∈ Finset.Ico 2 (N + 1), stableChargeFourth N k i j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hle := (Finset.mem_Ico.mp hj).1
    simpa only [Nat.sub_add_cancel hle] using coeff_stableLengthSummand_higher N i (j - 2) k
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : 2 ≤ N + 1), hhigher]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    coeff_stableLengthSummand_zero, coeff_stableLengthSummand_one]
  ring

/-- The stable length expression has the positive fermionic charge coefficient. -/
theorem coeff_stableLengthSeries_fermionic (N k : ℕ) (hN : 0 < N) :
    PowerSeries.coeff k (stableLengthSeries N k) = fermionicCoefficient N k := by
  rw [coeff_stableLengthSeries N k hN, fermionicCoefficient_eq_stableAlternatingCharge N k hN]

end TorusLinkHomology.HilbertSeries
