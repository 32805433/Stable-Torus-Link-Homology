import TorusLinkHomology.HilbertSeries.AlternatingGordon

/-! Finite product telescoping for the stable charge formula. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- A shifted Pochhammer tail, with support expressed before subtraction. -/
def stablePochhammerTail (a : ChargeSeries) (l i : ℕ) : ChargeSeries :=
  if i ≤ l then qPochhammer (-a * MvPowerSeries.X 1) (MvPowerSeries.X 1) (l - i) *
    gordonDenominator (l - i) else 0

/-- The summands whose finite sum eliminates the interior Gordon index. -/
def stablePochhammerDifference (a : ChargeSeries) (l i : ℕ) : ChargeSeries :=
  if i ≤ l then (MvPowerSeries.X 1) ^ (l - i) *
    qPochhammer (-a) (MvPowerSeries.X 1) (l - i) * gordonDenominator (l - i) else 0

theorem stablePochhammerTail_sub (a : ChargeSeries) (l i : ℕ) :
    stablePochhammerTail a l i - stablePochhammerTail a l (i + 1) =
      stablePochhammerDifference a l i := by
  by_cases hi : i ≤ l
  · by_cases hs : i + 1 ≤ l
    · let m := l - (i + 1)
      have hm : l - i = m + 1 := by dsimp [m]; omega
      simp only [stablePochhammerTail, stablePochhammerDifference, if_pos hi, if_pos hs, hm]
      change qPochhammer (-a * MvPowerSeries.X 1) (MvPowerSeries.X 1) (m + 1) *
          gordonDenominator (m + 1) -
          qPochhammer (-a * MvPowerSeries.X 1) (MvPowerSeries.X 1) m * gordonDenominator m = _
      rw [qPochhammer_succ, qPochhammer_shift, ← gordonDenominator_step m]
      rw [pow_succ']
      ring
    · have hl : l = i := by omega
      subst l
      simp [stablePochhammerTail, stablePochhammerDifference, hs]
  · have hs : ¬ i + 1 ≤ l := by omega
    simp [stablePochhammerTail, stablePochhammerDifference, hi, hs]

theorem sum_stablePochhammerDifference (a : ChargeSeries) (l N : ℕ) (hN : 1 ≤ N) :
    ∑ i ∈ Finset.Ico 1 N, stablePochhammerDifference a l i =
      stablePochhammerTail a l 1 - stablePochhammerTail a l N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, ih, ← stablePochhammerTail_sub]
    ring

/-- The negative Gordon terms telescope to two boundary contributions. -/
theorem stablePochhammer_negative_sum (a : ChargeSeries) (l N : ℕ) (hN : 1 ≤ N) :
    (1 + a) * stablePochhammerTail a l N +
        a * ∑ i ∈ Finset.Ico 1 N, stablePochhammerDifference a l i =
      a * stablePochhammerTail a l 1 + stablePochhammerTail a l N := by
  rw [sum_stablePochhammerDifference a l N hN]
  ring

/-- Summation by parts for the positive Gordon terms, with arbitrary
coefficient sequence. -/
theorem stable_sum_by_parts {S : Type*} [CommRing S]
    (q : S) (Q : ℕ → S) (r n : ℕ) :
    Q r + ∑ l ∈ Finset.range n, (Q (r + l + 1) - Q (r + l)) * q ^ (l + 1) =
      q ^ n * Q (r + n) + (1 - q) * ∑ l ∈ Finset.range n, q ^ l * Q (r + l) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [← add_assoc, ih, pow_succ]
    ring_nf

/-- Pochhammer specialization of summation by parts. -/
theorem stablePochhammer_positive_sum (y v q : ChargeSeries) (r n : ℕ) :
    qPochhammer (-y) v r +
        y * ∑ l ∈ Finset.range n, v ^ (r + l) * qPochhammer (-y) v (r + l) * q ^ (l + 1) =
      q ^ n * qPochhammer (-y) v (r + n) +
        (1 - q) * ∑ l ∈ Finset.range n, q ^ l * qPochhammer (-y) v (r + l) := by
  convert stable_sum_by_parts q (qPochhammer (-y) v) r n using 1
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [qPochhammer_succ]
  ring

theorem stable_sum_Ico_reverse {S : Type*} [AddCommMonoid S]
    (f : ℕ → S) (N : ℕ) :
    ∑ i ∈ Finset.Ico 1 N, f i = ∑ l ∈ Finset.range (N - 1), f (N - 1 - l) := by
  apply Finset.sum_bij (fun i _ => N - 1 - i)
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [Finset.mem_range]
    omega
  · intro i hi j hj he
    simp only [Finset.mem_Ico] at hi hj
    omega
  · intro l hl
    simp only [Finset.mem_range] at hl
    refine ⟨N - 1 - l, ?_, ?_⟩
    · simp only [Finset.mem_Ico]
      omega
    · omega
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    congr 1
    omega

/-- A finite polynomial window appearing in the cancellation correction. -/
def stablePochhammerWindow (N k j : ℕ) : ChargeSeries :=
  ∑ l ∈ Finset.range (N - 1), (MvPowerSeries.X 1) ^ (j * l) *
    qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k + 1 - N + l)

theorem alternatingGordonPositive_index (N i k j : ℕ) (hi : i ≤ N) :
    alternatingGordonPositive N i k j =
      (MvPowerSeries.X 1 : ChargeSeries) ^ ((N - i) * j) *
        alternatingGordonPositive N N k j := by
  unfold alternatingGordonPositive
  split_ifs with hk
  · have hb := alternatingGordon_exponent_bound N N j (k - N * j) (le_refl _)
    have hsub := Nat.sub_add_cancel hi
    have hsub' := congrArg (fun x => x * j) hsub
    simp only [Nat.add_mul] at hsub'
    have he : quadraticExponent N j + j * (k - N * j + 1) - i * j =
        (N - i) * j +
        (quadraticExponent N j + j * (k - N * j + 1) - N * j) := by omega
    rw [he, pow_add]
    ring
  · simp

theorem stablePositive_inner_sum (N k j : ℕ) (hN : 0 < N) (hk : N - 1 ≤ k) :
    qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k + 1 - N) *
        alternatingGordonPositive N N k j +
      MvPowerSeries.X 0 * ∑ i ∈ Finset.Ico 1 N,
        (MvPowerSeries.X 1) ^ (k - i) *
        qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k - i) *
        alternatingGordonPositive N i k j =
      qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) k *
        (MvPowerSeries.X 1) ^ ((N - 1) * j) * alternatingGordonPositive N N k j +
      alternatingGordonCorrection N N k j * stablePochhammerWindow N k j := by
  have hreindex : (∑ i ∈ Finset.Ico 1 N,
      (MvPowerSeries.X 1 : ChargeSeries) ^ (k - i) *
      qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k - i) *
      alternatingGordonPositive N i k j) =
      (∑ l ∈ Finset.range (N - 1),
        (MvPowerSeries.X 1) ^ (k + 1 - N + l) *
        qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k + 1 - N + l) *
        ((MvPowerSeries.X 1) ^ j) ^ (l + 1)) * alternatingGordonPositive N N k j := by
    rw [stable_sum_Ico_reverse, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    have hl' : l < N - 1 := Finset.mem_range.mp hl
    have hi : N - 1 - l ≤ N := by omega
    rw [alternatingGordonPositive_index N (N - 1 - l) k j hi]
    have he : k - (N - 1 - l) = k + 1 - N + l := by omega
    have he' : N - (N - 1 - l) = l + 1 := by omega
    rw [he, he', pow_mul]
    ring
  rw [hreindex]
  have he := stablePochhammer_positive_sum (MvPowerSeries.X 0) (MvPowerSeries.X 1)
    ((MvPowerSeries.X 1) ^ j) (k + 1 - N) (N - 1)
  have hsum : k + 1 - N + (N - 1) = k := by omega
  rw [hsum] at he
  have hc : alternatingGordonCorrection N N k j =
      alternatingGordonPositive N N k j * (1 - (MvPowerSeries.X 1 : ChargeSeries) ^ j) := by
    unfold alternatingGordonCorrection alternatingGordonPositive
    split_ifs <;> ring
  rw [hc]
  simp only [stablePochhammerWindow, ← pow_mul] at he ⊢
  have hm : j * (N - 1) = (N - 1) * j := Nat.mul_comm _ _
  rw [hm] at he
  linear_combination alternatingGordonPositive N N k j * he

/-- Common signed factor for the two negative stable-charge contributions. -/
def stableChargePrefactor (N k j : ℕ) : ChargeSeries :=
  (-1) ^ j * (MvPowerSeries.X 1) ^
    (quadraticExponent N j + j * (k - N * j + 1)) * gordonDenominator j *
    qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (N * j)

/-- The second and third sums of the stable alternating charge expression,
written together using supported Pochhammer tails. -/
def stableChargeBoundary (N k j : ℕ) : ChargeSeries :=
  if N * j ≤ k then
    stableChargePrefactor N k j *
      ((MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j)) *
          stablePochhammerTail (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j))
            (k - N * j) 1 +
        stablePochhammerTail (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j))
          (k - N * j) N)
  else 0

theorem stableNegative_term (N k j i : ℕ) (hnj : N * j ≤ k) :
    (MvPowerSeries.X 1 : ChargeSeries) ^ (k - i) *
        qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k - i) *
        alternatingGordonNegative N i k j =
      stableChargePrefactor N k j * MvPowerSeries.X 1 ^ (N * j) *
        stablePochhammerDifference (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j))
          (k - N * j) i := by
  have hi : N * j + i ≤ k ↔ i ≤ k - N * j := by omega
  unfold alternatingGordonNegative stablePochhammerDifference stableChargePrefactor
  simp only [hi]
  split_ifs with hs
  · have hsum : k - i = N * j + (k - N * j - i) := by omega
    rw [hsum, qPochhammer_add, pow_add]
    rw [neg_mul]
    ring
  · simp

theorem stableNegative_endpoint (N k j : ℕ) (hnj : N * j ≤ k) :
    qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k + 1 - N) *
        alternatingGordonNegative N N k j =
      stableChargePrefactor N k j *
        (1 + MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j)) *
        stablePochhammerTail (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j))
          (k - N * j) N := by
  have hi : N * j + N ≤ k ↔ N ≤ k - N * j := by omega
  unfold alternatingGordonNegative stablePochhammerTail stableChargePrefactor
  simp only [hi]
  split_ifs with hs
  · have hsum : k + 1 - N = N * j + ((k - N * j - N) + 1) := by omega
    rw [hsum, qPochhammer_add, qPochhammer_shift]
    simp only [neg_mul, sub_neg_eq_add]
    ring
  · simp

theorem stableNegative_inner_sum (N k j : ℕ) (hN : 0 < N) :
    qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k + 1 - N) *
        alternatingGordonNegative N N k j +
      MvPowerSeries.X 0 * ∑ i ∈ Finset.Ico 1 N,
        (MvPowerSeries.X 1) ^ (k - i) *
        qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k - i) *
        alternatingGordonNegative N i k j = stableChargeBoundary N k j := by
  by_cases hnj : N * j ≤ k
  · rw [stableChargeBoundary, if_pos hnj, stableNegative_endpoint N k j hnj]
    simp_rw [stableNegative_term N k j _ hnj]
    rw [← Finset.mul_sum]
    have he := stablePochhammer_negative_sum
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j)) (k - N * j) N hN
    linear_combination stableChargePrefactor N k j * he
  · have hz (i : ℕ) : alternatingGordonNegative N i k j = 0 := by
      simp [alternatingGordonNegative, show ¬ N * j + i ≤ k by omega]
    simp [stableChargeBoundary, hnj, hz]

/-- A supported finite form of the draft's four alternating charge sums.
The two middle sums are combined in `stableChargeBoundary`; the last is
written using the shifted negative Gordon summand and a finite window. -/
def stableAlternatingCoefficient (N k : ℕ) : ChargeSeries :=
  if k < N - 1 then
    qPochhammer (-MvPowerSeries.X 0 * MvPowerSeries.X 1) (MvPowerSeries.X 1) k *
      gordonDenominator k
  else
    ∑ j ∈ Finset.range (k + 1),
      (qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) k *
        (MvPowerSeries.X 1) ^ ((N - 1) * j) * alternatingGordonPositive N N k j -
      stableChargeBoundary N k j -
      (MvPowerSeries.X 1) ^ (k + 1 - N) *
        alternatingGordonNegative N 1 (k + 1 - N) j * stablePochhammerWindow N k (j + 1))

/-- Finite cancellation identifies the stable alternating charge formula
with the positive fermionic expression, without a partition interpretation. -/
theorem fermionicCoefficient_eq_stableAlternating (N k : ℕ) (hN : 0 < N) :
    fermionicCoefficient N k = stableAlternatingCoefficient N k := by
  by_cases hklo : k < N - 1
  · simp [fermionicCoefficient, stableAlternatingCoefficient, hklo, gordonDenominator]
  have hk : N - 1 ≤ k := by omega
  unfold fermionicCoefficient stableAlternatingCoefficient
  rw [if_neg hklo, if_neg hklo, gordonCoefficient_eq_alternating N N k hN hN (le_refl _)]
  have hg : (∑ i ∈ Finset.Ico 1 N,
      (MvPowerSeries.X 1 : ChargeSeries) ^ (k - i) *
      qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k - i) * gordonCoefficient N i k) =
      ∑ i ∈ Finset.Ico 1 N,
        (MvPowerSeries.X 1) ^ (k - i) *
        qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k - i) *
        alternatingGordonCoefficient N i k := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    rw [gordonCoefficient_eq_alternating N i k hN hi'.1 (by omega)]
  rw [hg]
  have hreflect (j : ℕ) :
      (MvPowerSeries.X 1 : ChargeSeries) ^ (k + 1 - N) *
        alternatingGordonNegative N 1 (k + 1 - N) j =
      -alternatingGordonCorrection N N k (j + 1) := by
    have he : k - (N - 1) = k + 1 - N := by omega
    simpa [he] using alternatingGordonNegative_reflect N N k j hN (le_refl _) hk
  have htel (r : ℕ) :
      (∑ j ∈ Finset.range r,
        (alternatingGordonCorrection N N k j * stablePochhammerWindow N k j -
          alternatingGordonCorrection N N k (j + 1) * stablePochhammerWindow N k (j + 1))) =
        alternatingGordonCorrection N N k 0 * stablePochhammerWindow N k 0 -
          alternatingGordonCorrection N N k r * stablePochhammerWindow N k r := by
    induction r with
    | zero => simp
    | succ r ih => rw [Finset.sum_range_succ, ih]; ring
  have hend : alternatingGordonCorrection N N k (k + 1) = 0 := by
    have hle : k + 1 ≤ N * (k + 1) := by simpa using Nat.mul_le_mul_right (k + 1) hN
    simp [alternatingGordonCorrection, show ¬ N * (k + 1) ≤ k by omega]
  calc
    _ = ∑ j ∈ Finset.range (k + 1),
        ((qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k + 1 - N) *
            alternatingGordonPositive N N k j +
          MvPowerSeries.X 0 * ∑ i ∈ Finset.Ico 1 N,
            (MvPowerSeries.X 1) ^ (k - i) *
            qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k - i) *
            alternatingGordonPositive N i k j) -
        (qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k + 1 - N) *
            alternatingGordonNegative N N k j +
          MvPowerSeries.X 0 * ∑ i ∈ Finset.Ico 1 N,
            (MvPowerSeries.X 1) ^ (k - i) *
            qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (k - i) *
            alternatingGordonNegative N i k j)) := by
      simp only [alternatingGordonCoefficient, Finset.mul_sum, mul_sub,
        Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_comm (s := Finset.Ico 1 N) (t := Finset.range (k + 1)),
        Finset.sum_comm (s := Finset.Ico 1 N) (t := Finset.range (k + 1))]
      ring
    _ = ∑ j ∈ Finset.range (k + 1),
        ((qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) k *
          (MvPowerSeries.X 1) ^ ((N - 1) * j) * alternatingGordonPositive N N k j -
          stableChargeBoundary N k j -
          (MvPowerSeries.X 1) ^ (k + 1 - N) *
            alternatingGordonNegative N 1 (k + 1 - N) j * stablePochhammerWindow N k (j + 1)) +
        (alternatingGordonCorrection N N k j * stablePochhammerWindow N k j -
          alternatingGordonCorrection N N k (j + 1) * stablePochhammerWindow N k (j + 1))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [stablePositive_inner_sum N k j hN hk, stableNegative_inner_sum N k j hN, hreflect]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, htel, alternatingGordonCorrection_zero, hend]
      ring

/-- First sum in the stable alternating charge formula. -/
def stableChargeFirst (N k j : ℕ) : ChargeSeries :=
  if N * j ≤ k then
    (-1) ^ j * MvPowerSeries.X 1 ^ (quadraticExponent N j + j * (k - N * j)) *
      qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) k *
      gordonDenominator j * gordonDenominator (k - N * j)
  else 0

/-- Second sum, including its prefactor y. The support guard makes charge zero empty. -/
def stableChargeSecond (N k j : ℕ) : ChargeSeries :=
  if N * j + 1 ≤ k then
    MvPowerSeries.X 0 * (-1) ^ j *
      MvPowerSeries.X 1 ^ (quadraticExponent N j + j * (k - N * j - 1 + N + 2)) *
      qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (N * j) *
      qPochhammer (-MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j + 1))
        (MvPowerSeries.X 1) (k - N * j - 1) *
      gordonDenominator j * gordonDenominator (k - N * j - 1)
  else 0

/-- Third sum, supported in charge at least N. -/
def stableChargeThird (N k j : ℕ) : ChargeSeries :=
  if N * j + N ≤ k then
    (-1) ^ j * MvPowerSeries.X 1 ^
        (quadraticExponent N j + j * (k - N * j - N + N + 1)) *
      qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) (N * j) *
      qPochhammer (-MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j + 1))
        (MvPowerSeries.X 1) (k - N * j - N) *
      gordonDenominator j * gordonDenominator (k - N * j - N)
  else 0

/-- Inner summand of the fourth sum, with indices 2 ≤ i ≤ N. -/
def stableChargeFourth (N k j i : ℕ) : ChargeSeries :=
  if N * j + N ≤ k then
    (-1) ^ j * MvPowerSeries.X 1 ^
        (quadraticExponent N j + j * (k - N * j - N + N + i) +
          (k - N * j - N) + i - 1) *
      qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1)
        (N * j + (k - N * j - N) + i - 1) *
      gordonDenominator j * gordonDenominator (k - N * j - N)
  else 0

/-- The draft's four finite alternating charge sums, with safe addition-based support. -/
def stableAlternatingCharge (N k : ℕ) : ChargeSeries :=
  ∑ j ∈ Finset.range (k + 1),
    (stableChargeFirst N k j - stableChargeSecond N k j - stableChargeThird N k j -
      ∑ i ∈ Finset.Ico 2 (N + 1), stableChargeFourth N k j i)

theorem stableChargeFirst_eq (N k j : ℕ) (hN : 0 < N) :
    stableChargeFirst N k j =
      qPochhammer (-MvPowerSeries.X 0) (MvPowerSeries.X 1) k *
        (MvPowerSeries.X 1) ^ ((N - 1) * j) * alternatingGordonPositive N N k j := by
  unfold stableChargeFirst alternatingGordonPositive
  split_ifs with hnj
  · have hb := alternatingGordon_exponent_bound N N j (k - N * j) (le_refl _)
    have hn := congrArg (fun x => x * j) (Nat.sub_add_cancel hN)
    simp only [Nat.add_mul, Nat.one_mul] at hn
    have he : (N - 1) * j +
        (quadraticExponent N j + j * (k - N * j + 1) - N * j) =
        quadraticExponent N j + j * (k - N * j) := by
      have hh := Nat.sub_add_cancel hb
      nlinarith
    rw [← he, pow_add]
    ring
  · simp

theorem stableChargeBoundary_eq (N k j : ℕ) :
    stableChargeBoundary N k j = stableChargeSecond N k j + stableChargeThird N k j := by
  unfold stableChargeBoundary
  by_cases hnj : N * j ≤ k
  · rw [if_pos hnj]
    have hsecond : stableChargePrefactor N k j *
        ((MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j)) *
          stablePochhammerTail (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j))
            (k - N * j) 1) = stableChargeSecond N k j := by
      unfold stableChargePrefactor stablePochhammerTail stableChargeSecond
      have hi : N * j + 1 ≤ k ↔ 1 ≤ k - N * j := by omega
      simp only [hi]
      split_ifs with hs
      · have he : quadraticExponent N j + j * (k - N * j - 1 + N + 2) =
            (quadraticExponent N j + j * (k - N * j + 1)) + N * j := by
          have hh := Nat.sub_add_cancel hs
          have hh' := congrArg (fun x => j * x) hh
          nlinarith
        rw [he, pow_add]
        simp only [pow_succ, neg_mul, mul_assoc]
        ring
      · simp
    have hthird : stableChargePrefactor N k j *
        stablePochhammerTail (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ (N * j))
          (k - N * j) N = stableChargeThird N k j := by
      unfold stableChargePrefactor stablePochhammerTail stableChargeThird
      have hi : N * j + N ≤ k ↔ N ≤ k - N * j := by omega
      simp only [hi]
      split_ifs with hs
      · rw [Nat.sub_add_cancel hs]
        simp only [pow_succ, neg_mul, mul_assoc]
        ring
      · simp
    rw [mul_add, hsecond, hthird]
  · have hsecond : ¬ N * j + 1 ≤ k := by omega
    have hthird : ¬ N * j + N ≤ k := by omega
    simp [hnj, stableChargeSecond, stableChargeThird, hsecond, hthird]

theorem stableChargeFourth_sum_eq (N k j : ℕ) (hN : 0 < N) (hk : N - 1 ≤ k) :
    (∑ i ∈ Finset.Ico 2 (N + 1), stableChargeFourth N k j i) =
      (MvPowerSeries.X 1 : ChargeSeries) ^ (k + 1 - N) *
        alternatingGordonNegative N 1 (k + 1 - N) j * stablePochhammerWindow N k (j + 1) := by
  have hsupport : N * j + 1 ≤ k + 1 - N ↔ N * j + N ≤ k := by omega
  unfold alternatingGordonNegative
  simp only [hsupport]
  by_cases hs : N * j + N ≤ k
  · rw [if_pos hs]
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : N + 1 - 2 = N - 1 := by omega
    rw [hlen]
    unfold stablePochhammerWindow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    unfold stableChargeFourth
    rw [if_pos hs]
    have hden : k + 1 - N - N * j - 1 = k - N * j - N := by omega
    have hprod : N * j + (k - N * j - N) + (2 + l) - 1 = k + 1 - N + l := by omega
    have he : quadraticExponent N j + j * (k - N * j - N + N + (2 + l)) +
        (k - N * j - N) + (2 + l) - 1 =
        (k + 1 - N) + (quadraticExponent N j + j * (k + 1 - N - N * j + 1)) +
          (j + 1) * l := by
      have hr : k + 1 - N = N * j + (k - N * j - N) + 1 := by omega
      have hr' : k + 1 - N - N * j + 1 = k - N * j - N + 2 := by omega
      rw [hr']
      have hb : 1 ≤ quadraticExponent N j + j * (k - N * j - N + N + (2 + l)) +
          (k - N * j - N) + (2 + l) := by omega
      have hh := Nat.sub_add_cancel hb
      nlinarith
    rw [hden, hprod, he, pow_add, pow_add]
    ring
  · simp only [if_neg hs, mul_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro i hi
    simp [stableChargeFourth, hs]

/-- The literal four-sum expression and its compact supported form agree
in the high-charge range. -/
theorem stableAlternatingCharge_high (N k : ℕ) (hN : 0 < N) (hk : N - 1 ≤ k) :
    stableAlternatingCharge N k = stableAlternatingCoefficient N k := by
  rw [stableAlternatingCoefficient, if_neg (by omega)]
  unfold stableAlternatingCharge
  apply Finset.sum_congr rfl
  intro j hj
  rw [stableChargeFirst_eq N k j hN, stableChargeBoundary_eq,
    stableChargeFourth_sum_eq N k j hN hk]
  ring

theorem stablePochhammer_low_charge_identity (y : ChargeSeries) (k : ℕ) :
    qPochhammer (-y) (MvPowerSeries.X 1) k * gordonDenominator k -
        (if 1 ≤ k then y * qPochhammer (-y * MvPowerSeries.X 1) (MvPowerSeries.X 1)
          (k - 1) * gordonDenominator (k - 1) else 0) =
      qPochhammer (-y * MvPowerSeries.X 1) (MvPowerSeries.X 1) k * gordonDenominator k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [if_pos (by omega), Nat.add_sub_cancel, qPochhammer_shift,
      qPochhammer_succ, ← gordonDenominator_step k]
    rw [pow_succ']
    ring

theorem stableAlternatingCharge_low (N k : ℕ) (hk : k < N - 1) :
    stableAlternatingCharge N k =
      qPochhammer (-MvPowerSeries.X 0 * MvPowerSeries.X 1) (MvPowerSeries.X 1) k *
        gordonDenominator k := by
  unfold stableAlternatingCharge
  rw [Finset.sum_eq_single 0]
  · have hN : ¬ N ≤ k := by omega
    simp only [stableChargeFirst, stableChargeSecond, stableChargeThird,
      stableChargeFourth, Nat.mul_zero, Nat.zero_le, ↓reduceIte,
      quadraticExponent_zero, zero_add, Nat.zero_mul, pow_zero, one_mul,
      Nat.sub_zero, gordonDenominator_zero, mul_one, qPochhammer_zero, hN,
      Finset.sum_const_zero, sub_zero]
    convert stablePochhammer_low_charge_identity (MvPowerSeries.X 0) k using 1; simp
  · intro j hj hj0
    have hpos : 1 ≤ j := by omega
    have hle : N ≤ N * j := by simpa using Nat.mul_le_mul_left N hpos
    have hfirst : ¬ N * j ≤ k := by omega
    have hsecond : ¬ N * j + 1 ≤ k := by omega
    have hthird : ¬ N * j + N ≤ k := by omega
    simp [stableChargeFirst, stableChargeSecond, stableChargeThird,
      stableChargeFourth, hfirst, hsecond, hthird]
  · simp

/-- Identification with the draft's literal four finite alternating sums. -/
theorem fermionicCoefficient_eq_stableAlternatingCharge (N k : ℕ) (hN : 0 < N) :
    fermionicCoefficient N k = stableAlternatingCharge N k := by
  rw [fermionicCoefficient_eq_stableAlternating N k hN]
  by_cases hk : k < N - 1
  · rw [stableAlternatingCharge_low N k hk]
    simp [stableAlternatingCoefficient, hk]
  · exact (stableAlternatingCharge_high N k hN (by omega)).symm

end TorusLinkHomology.HilbertSeries
