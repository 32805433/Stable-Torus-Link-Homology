import TorusLinkHomology.HilbertSeries.Gordon
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! The finite alternating Gordon expression. All exponents are combined
before natural subtraction, so no inverse of the formal variable is used. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- Reciprocal of the ordinary finite q-factorial. -/
def gordonDenominator (m : ℕ) : ChargeSeries :=
  (qPochhammer (MvPowerSeries.X 1) (MvPowerSeries.X 1) m)⁻¹

@[simp] theorem gordonDenominator_zero : gordonDenominator 0 = 1 := by
  simp [gordonDenominator]

theorem gordonDenominator_step (m : ℕ) :
    (1 - (MvPowerSeries.X 1 : ChargeSeries) ^ (m + 1)) * gordonDenominator (m + 1) =
      gordonDenominator m :=
  qPochhammer_inv_step _ (by simp) m

theorem gordonDenominator_sub (m : ℕ) :
    gordonDenominator (m + 1) - gordonDenominator m =
      (MvPowerSeries.X 1 : ChargeSeries) ^ (m + 1) * gordonDenominator (m + 1) := by
  have h := gordonDenominator_step m
  linear_combination h

/-- The first term of the fixed-charge alternating formula. -/
def alternatingGordonPositive (N i k j : ℕ) : ChargeSeries :=
  if N * j ≤ k then
    (-1) ^ j * (MvPowerSeries.X 1) ^
      (quadraticExponent N j + j * (k - N * j + 1) - i * j) *
      gordonDenominator j * gordonDenominator (k - N * j)
  else 0

/-- The second term, supported only when its denominator index is nonnegative. -/
def alternatingGordonNegative (N i k j : ℕ) : ChargeSeries :=
  if N * j + i ≤ k then
    (-1) ^ j * (MvPowerSeries.X 1) ^
      (quadraticExponent N j + j * (k - N * j + 1)) *
      gordonDenominator j * gordonDenominator (k - N * j - i)
  else 0

/-- The two finite sums obtained by extracting charge from the alternating
Gordon expression. The upper bound k is sufficient whenever N is positive. -/
def alternatingGordonCoefficient (N i k : ℕ) : ChargeSeries :=
  ∑ j ∈ Finset.range (k + 1),
    (alternatingGordonPositive N i k j - alternatingGordonNegative N i k j)

@[simp] theorem alternatingGordonCoefficient_zero_index (N k : ℕ) :
    alternatingGordonCoefficient N 0 k = 0 := by
  simp [alternatingGordonCoefficient, alternatingGordonPositive, alternatingGordonNegative]

@[simp] theorem alternatingGordonCoefficient_zero_charge (N i : ℕ) (hi : 0 < i) :
    alternatingGordonCoefficient N i 0 = 1 := by
  simp [alternatingGordonCoefficient, alternatingGordonPositive, alternatingGordonNegative,
    Nat.ne_of_gt hi]

/-- The apparent negative power in the printed Gordon expression is absorbed
by the quadratic exponent, even at endpoint index i=N. -/
theorem alternatingGordon_exponent_bound (N i j l : ℕ) (hi : i ≤ N) :
    i * j ≤ quadraticExponent N j + j * (l + 1) := by
  have h := quadraticExponent_ge_linear N j
  have hi' := Nat.mul_le_mul_right j hi
  omega

/-- At charge below N the alternating formula has only its j=0 term. -/
theorem alternatingGordonCoefficient_small_charge (N i k : ℕ) (hk : k < N) :
    alternatingGordonCoefficient N i k =
      gordonDenominator k - if i ≤ k then gordonDenominator (k - i) else 0 := by
  classical
  unfold alternatingGordonCoefficient
  rw [Finset.sum_eq_single 0]
  · simp [alternatingGordonPositive, alternatingGordonNegative]
  · intro j hj hj0
    have hpos : 1 ≤ j := by omega
    have hle : N ≤ N * j := by simpa using Nat.mul_le_mul_left N hpos
    have hnk : ¬ N * j ≤ k := by omega
    have hni : ¬ N * j + i ≤ k := by omega
    simp [alternatingGordonPositive, alternatingGordonNegative, hnk, hni]
  · simp

/-- The correction that telescopes in the alternating Gordon recurrence. -/
def alternatingGordonCorrection (N i k j : ℕ) : ChargeSeries :=
  if N * j ≤ k then
    (-1) ^ j * (MvPowerSeries.X 1) ^
      (quadraticExponent N j + j * (k - N * j + 1) - i * j) *
      (1 - (MvPowerSeries.X 1) ^ j) *
      gordonDenominator j * gordonDenominator (k - N * j)
  else 0

@[simp] theorem alternatingGordonCorrection_zero (N i k : ℕ) :
    alternatingGordonCorrection N i k 0 = 0 := by
  simp [alternatingGordonCorrection]

theorem alternatingGordonPositive_sub (N i k j : ℕ)
    (hi : 1 ≤ i) (hiN : i ≤ N) :
    alternatingGordonPositive N i k j - alternatingGordonPositive N (i - 1) k j =
      alternatingGordonCorrection N i k j := by
  unfold alternatingGordonPositive alternatingGordonCorrection
  split_ifs with hk
  · have hb := alternatingGordon_exponent_bound N i j (k - N * j) hiN
    have hm : (i - 1) * j + j = i * j := by
      simpa only [Nat.add_mul, Nat.one_mul] using
        congrArg (fun x => x * j) (Nat.sub_add_cancel hi)
    have he : quadraticExponent N j + j * (k - N * j + 1) - (i - 1) * j =
        (quadraticExponent N j + j * (k - N * j + 1) - i * j) + j := by omega
    rw [he, pow_add]
    ring
  · ring

theorem alternatingGordonNegative_sub (N i k j : ℕ)
    (hi : 1 ≤ i) (hiN : i ≤ N) :
    alternatingGordonNegative N (i - 1) k j - alternatingGordonNegative N i k j =
      if i - 1 ≤ k then
        (MvPowerSeries.X 1 : ChargeSeries) ^ (k - (i - 1)) *
          alternatingGordonPositive N (N - i + 1) (k - (i - 1)) j else 0 := by
  by_cases hk : i - 1 ≤ k
  · rw [if_pos hk]
    by_cases hnj : N * j ≤ k - (i - 1)
    · have hprev : N * j + (i - 1) ≤ k := by omega
      let m := k - (N * j + (i - 1))
      have hkm : k = N * j + (i - 1) + m := by dsimp [m]; omega
      have hres : k - N * j - (i - 1) = m := by omega
      have hres' : k - (i - 1) - N * j = m := by omega
      have hsum : k - N * j + 1 = i + m := by omega
      have hmul : (N - i + 1) * j + (i - 1) * j = N * j := by
        rw [← Nat.add_mul]
        congr 1
        omega
      have hb := alternatingGordon_exponent_bound N (N - i + 1) j m (by omega)
      have he : (k - (i - 1)) +
          (quadraticExponent N j + j * (m + 1) - (N - i + 1) * j) =
          (quadraticExponent N j + j * (i + m)) + m := by
        have hh := Nat.sub_add_cancel hb
        have hki := Nat.sub_add_cancel hk
        have hii := Nat.sub_add_cancel hi
        nlinarith
      unfold alternatingGordonNegative alternatingGordonPositive
      rw [if_pos hprev, if_pos hnj, hres, hres', hsum]
      have hrhs : (MvPowerSeries.X 1 : ChargeSeries) ^ (k - (i - 1)) *
          ((-1) ^ j * MvPowerSeries.X 1 ^
            (quadraticExponent N j + j * (m + 1) - (N - i + 1) * j) *
            gordonDenominator j * gordonDenominator m) =
          (-1) ^ j * MvPowerSeries.X 1 ^ (quadraticExponent N j + j * (i + m)) *
            gordonDenominator j * (MvPowerSeries.X 1 ^ m * gordonDenominator m) := by
        calc
          _ = (-1) ^ j *
              (MvPowerSeries.X 1 ^ (k - (i - 1)) *
                MvPowerSeries.X 1 ^ (quadraticExponent N j + j * (m + 1) -
                  (N - i + 1) * j)) * gordonDenominator j * gordonDenominator m := by ring
          _ = _ := by rw [← pow_add, he, pow_add]; ring
      rw [hrhs]
      cases hm : m with
      | zero =>
        have hno : ¬ N * j + i ≤ k := by omega
        simp [if_neg hno]
      | succ t =>
        have hy : N * j + i ≤ k := by omega
        have ht : k - N * j - i = t := by omega
        rw [if_pos hy, ht]
        have hd := gordonDenominator_sub t
        linear_combination (-1 : ChargeSeries) ^ j *
          MvPowerSeries.X 1 ^ (quadraticExponent N j + j * (i + (t + 1))) *
          gordonDenominator j * hd
    · have hno : ¬ N * j + (i - 1) ≤ k := by omega
      have hno' : ¬ N * j + i ≤ k := by omega
      simp [alternatingGordonNegative, alternatingGordonPositive, hno, hno', hnj]
  · have hno : ¬ N * j + (i - 1) ≤ k := by omega
    have hno' : ¬ N * j + i ≤ k := by omega
    simp [alternatingGordonNegative, hk, hno, hno']

theorem alternatingGordonNegative_reflect (N i k j : ℕ)
    (hi : 1 ≤ i) (hiN : i ≤ N) (hk : i - 1 ≤ k) :
    (MvPowerSeries.X 1 : ChargeSeries) ^ (k - (i - 1)) *
        alternatingGordonNegative N (N - i + 1) (k - (i - 1)) j =
      -alternatingGordonCorrection N i k (j + 1) := by
  have hmul : N * (j + 1) = N * j + N := by ring
  have href : N * j + (N - i + 1) ≤ k - (i - 1) ↔ N * (j + 1) ≤ k := by
    have hn : N - i + i = N := Nat.sub_add_cancel hiN
    omega
  unfold alternatingGordonNegative alternatingGordonCorrection
  simp only [href]
  split_ifs with hsupport
  · let l := k - N * (j + 1)
    have hl : k = N * (j + 1) + l := by dsimp [l]; omega
    have hden : k - (i - 1) - N * j - (N - i + 1) = l := by
      have hn : N - i + i = N := Nat.sub_add_cancel hiN
      omega
    have hsum : k - (i - 1) - N * j + 1 + i = N + l + 2 := by omega
    have hsum' : k - (i - 1) + i = N * j + N + l + 1 := by omega
    have hb := alternatingGordon_exponent_bound N i (j + 1) l hiN
    have he : (k - (i - 1)) +
        (quadraticExponent N j + j * (k - (i - 1) - N * j + 1)) =
        quadraticExponent N (j + 1) + (j + 1) * (l + 1) - i * (j + 1) := by
      have hq := quadraticExponent_succ N j
      have ht := Nat.sub_add_cancel hb
      have ht' := congrArg (fun x => j * x) hsum
      nlinarith
    rw [hden]
    change _ = -((-1) ^ (j + 1) * MvPowerSeries.X 1 ^
      (quadraticExponent N (j + 1) + (j + 1) * (l + 1) - i * (j + 1)) *
      (1 - MvPowerSeries.X 1 ^ (j + 1)) * gordonDenominator (j + 1) *
      gordonDenominator l)
    calc
      _ = (-1) ^ j * MvPowerSeries.X 1 ^
          ((k - (i - 1)) + (quadraticExponent N j +
            j * (k - (i - 1) - N * j + 1))) * gordonDenominator j *
          gordonDenominator l := by rw [pow_add]; ring
      _ = (-1) ^ j * MvPowerSeries.X 1 ^
          (quadraticExponent N (j + 1) + (j + 1) * (l + 1) - i * (j + 1)) *
          ((1 - MvPowerSeries.X 1 ^ (j + 1)) * gordonDenominator (j + 1)) *
          gordonDenominator l := by rw [he, gordonDenominator_step]
      _ = _ := by rw [pow_succ]; ring
  · simp

theorem alternatingGordon_terms_vanish (N i k j : ℕ) (hN : 0 < N) (hk : k < j) :
    alternatingGordonPositive N i k j = 0 ∧ alternatingGordonNegative N i k j = 0 := by
  have hn : j ≤ N * j := by simpa using Nat.mul_le_mul_right j hN
  have ha : ¬ N * j ≤ k := by omega
  have hb : ¬ N * j + i ≤ k := by omega
  simp [alternatingGordonPositive, alternatingGordonNegative, ha, hb]

theorem sum_alternatingGordon_terms (N i k K : ℕ) (hN : 0 < N) (hk : k ≤ K) :
    ∑ j ∈ Finset.range (K + 1),
        (alternatingGordonPositive N i k j - alternatingGordonNegative N i k j) =
      alternatingGordonCoefficient N i k := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hjk
  have hlt : k < j := by simpa using hjk
  obtain ⟨hp, hn⟩ := alternatingGordon_terms_vanish N i k j hN hlt
  simp [hp, hn]

/-- The alternating sums satisfy exactly the same recurrence as the explicit
Gordon multisums; the correction terms cancel at both finite endpoints. -/
theorem alternatingGordonCoefficient_recurrence (N i k : ℕ)
    (hi : 1 ≤ i) (hiN : i ≤ N) :
    alternatingGordonCoefficient N i k - alternatingGordonCoefficient N (i - 1) k =
      if i - 1 ≤ k then (MvPowerSeries.X 1 : ChargeSeries) ^ (k - (i - 1)) *
        alternatingGordonCoefficient N (N - i + 1) (k - (i - 1)) else 0 := by
  have hN : 0 < N := by omega
  by_cases hk : i - 1 ≤ k
  · rw [if_pos hk]
    have htel (r : ℕ) :
        (∑ j ∈ Finset.range r, (alternatingGordonCorrection N i k j -
          alternatingGordonCorrection N i k (j + 1))) =
          alternatingGordonCorrection N i k 0 - alternatingGordonCorrection N i k r := by
      induction r with
      | zero => simp
      | succ r ih => rw [Finset.sum_range_succ, ih]; ring
    have hend : alternatingGordonCorrection N i k (k + 1) = 0 := by
      have hle : k + 1 ≤ N * (k + 1) := by
        simpa using Nat.mul_le_mul_right (k + 1) hN
      simp [alternatingGordonCorrection, show ¬ N * (k + 1) ≤ k by omega]
    calc
      _ = ∑ j ∈ Finset.range (k + 1),
          ((alternatingGordonPositive N i k j - alternatingGordonPositive N (i - 1) k j) +
            (alternatingGordonNegative N (i - 1) k j - alternatingGordonNegative N i k j)) := by
        unfold alternatingGordonCoefficient
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ j ∈ Finset.range (k + 1),
          ((MvPowerSeries.X 1 : ChargeSeries) ^ (k - (i - 1)) *
            (alternatingGordonPositive N (N - i + 1) (k - (i - 1)) j -
              alternatingGordonNegative N (N - i + 1) (k - (i - 1)) j) +
            (alternatingGordonCorrection N i k j -
              alternatingGordonCorrection N i k (j + 1))) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [alternatingGordonPositive_sub N i k j hi hiN,
          alternatingGordonNegative_sub N i k j hi hiN, if_pos hk]
        have he := alternatingGordonNegative_reflect N i k j hi hiN hk
        linear_combination he
      _ = (MvPowerSeries.X 1 : ChargeSeries) ^ (k - (i - 1)) *
          alternatingGordonCoefficient N (N - i + 1) (k - (i - 1)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          sum_alternatingGordon_terms N (N - i + 1) (k - (i - 1)) k hN (by omega),
          htel, alternatingGordonCorrection_zero, hend]
        ring
  · rw [if_neg hk, alternatingGordonCoefficient_small_charge N i k (by omega),
      alternatingGordonCoefficient_small_charge N (i - 1) k (by omega)]
    simp [hk, show ¬ i ≤ k by omega]

/-- The explicit Gordon multisum equals its finite alternating expression. -/
theorem gordonCoefficient_eq_alternating (N i k : ℕ)
    (hN : 0 < N) (hi : 1 ≤ i) (hiN : i ≤ N) :
    gordonCoefficient N i k = alternatingGordonCoefficient N i k := by
  let : IsDomain ChargeSeries := NoZeroDivisors.to_isDomain _
  have hv : ∀ k : ℕ, 0 < k → (MvPowerSeries.X 1 : ChargeSeries) ^ k ≠ 1 := by
    intro k hk he
    have hc := congrArg MvPowerSeries.constantCoeff he
    simp [Nat.ne_of_gt hk] at hc
  have he := gordon_recurrence_unique (MvPowerSeries.X 1 : ChargeSeries) hv N hN
    (gordonFamily N) (alternatingGordonCoefficient N)
    (gordonFamily_zero_index N) (alternatingGordonCoefficient_zero_index N)
    (fun i hi hiN => by
      rw [gordonFamily_zero_charge N i hi, alternatingGordonCoefficient_zero_charge N i hi])
    (fun i k hi hiN => gordonFamily_recurrence N i k hi hiN)
    (fun i k hi hiN => alternatingGordonCoefficient_recurrence N i k hi hiN) k i hi hiN
  simpa [gordonFamily, show i ≠ 0 by omega] using he

end TorusLinkHomology.HilbertSeries
