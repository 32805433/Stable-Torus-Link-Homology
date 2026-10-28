import TorusLinkHomology.HilbertSeries.QSeries

/-! Boundary calculations for the explicit finite numerator. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- The length-one explicit sum reduces to the numerator of ℚ[u₀]/(u₀ᴺ). -/
theorem finiteNumerator_one (N : ℕ) (hN : 0 < N) :
    finiteNumerator N 1 = 1 - (MvPowerSeries.X 0 : Series) ^ N := by
  classical
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  unfold finiteNumerator
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  simp only [mul_zero, zero_add,
    pow_zero, one_mul, qPochhammer_zero, mul_one, quadraticExponent_zero]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hrest' : ∀ j : ℕ, ¬ j + 1 + 1 ≤ 1 := by omega
  simp only [hrest', ↓reduceIte, Finset.sum_const_zero, zero_add]
  norm_num [numeratorCorrection, qPochhammer, gaussianBinomial]
  ring

section InitialValues

variable {S : Type*} [CommRing S]

/-- The correction convolution giving the initial Hilbert numerators. -/
def initialNumerator (N : ℕ) (s v z : S) (n : ℕ) : S :=
  ∑ j ∈ Finset.range (n + 1), numeratorCorrection N s v z j *
    qPochhammer (-z * s ^ (N + 1) * v ^ j) v (n - j)

@[simp] theorem initialNumerator_zero (N : ℕ) (s v z : S) :
    initialNumerator N s v z 0 = 1 := by
  simp [initialNumerator, numeratorCorrection]

theorem initialNumerator_step (N n : ℕ) (s v z : S) :
    initialNumerator N s v z (n + 1) =
      (1 + z * s ^ (N + 1) * v ^ n) * initialNumerator N s v z n +
        numeratorCorrection N s v z (n + 1) := by
  unfold initialNumerator
  rw [Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.sub_self, qPochhammer_zero, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show n + 1 - j = (n - j) + 1 by omega, qPochhammer_succ]
  have he : (-z * s ^ (N + 1) * v ^ j) * v ^ (n - j) =
      -z * s ^ (N + 1) * v ^ n := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hjn]
  rw [he]
  ring

/-- The complete multiplied initial identity; no division by z occurs. -/
theorem initialNumerator_multiplied (N n : ℕ) (s v z : S) :
    z * initialNumerator N s v z (n + 1) =
      (1 + z) * qPochhammer (-z * s ^ (N + 1) * v) v n -
        qPochhammer (-z * s ^ N) v (n + 1) := by
  induction n with
  | zero =>
    rw [initialNumerator_step, initialNumerator_zero]
    simp only [Nat.zero_add, numeratorCorrection, qPochhammer_zero, qPochhammer_one, pow_zero, mul_one]
    rw [pow_succ]
    ring
  | succ n ih =>
    rw [initialNumerator_step]
    rw [mul_add, mul_left_comm z, ih]
    conv_rhs => rw [qPochhammer_succ, qPochhammer_succ]
    simp only [numeratorCorrection]
    rw [pow_succ s N, pow_succ v n]
    ring

end InitialValues

/-- Below the first recurrence shift, only the zero-th outer summand survives. -/
theorem finiteNumerator_eq_initial_of_le (N n : ℕ) (hn : n ≤ N) :
    finiteNumerator N n = initialNumerator N (MvPowerSeries.X 0)
      (MvPowerSeries.X 1) (MvPowerSeries.X 2) n := by
  classical
  unfold finiteNumerator
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, mul_zero, zero_mul, zero_add, quadraticExponent_zero, qPochhammer_zero,
      mul_one, one_mul, gaussianBinomial_zero_right, Nat.sub_zero]
    unfold initialNumerator
    rw [← Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hn 1))]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    · intro j hj hjn
      have hjn' : ¬ j ≤ n := by simpa using hjn
      rw [if_neg hjn']
  · intro i hi hi0
    apply Finset.sum_eq_zero
    intro j hj
    have hn' : ¬ (N + 1) * i + j ≤ n := by
      have hi' : 0 < i := Nat.pos_of_ne_zero hi0
      nlinarith
    rw [if_neg hn']
  · simp

/-- All strict short-range initial values of the explicit finite expression. -/
theorem finiteNumerator_initial_of_lt (N n : ℕ) (hn : n < N) :
    (MvPowerSeries.X 2 : Series) * finiteNumerator N (n + 1) =
      (1 + MvPowerSeries.X 2) *
        qPochhammer (-MvPowerSeries.X 2 * (MvPowerSeries.X 0 : Series) ^ (N + 1) *
          MvPowerSeries.X 1) (MvPowerSeries.X 1) n -
        qPochhammer (-MvPowerSeries.X 2 * (MvPowerSeries.X 0 : Series) ^ N)
          (MvPowerSeries.X 1) (n + 1) := by
  rw [finiteNumerator_eq_initial_of_le N (n + 1) hn]
  exact initialNumerator_multiplied _ _ _ _ _

/-- At the first recurrence boundary the next outer summand supplies the
missing correction term. -/
theorem finiteNumerator_eq_initial_boundary (N : ℕ) (hN : 0 < N) :
    finiteNumerator N (N + 1) = initialNumerator N (MvPowerSeries.X 0)
      (MvPowerSeries.X 1) (MvPowerSeries.X 2) (N + 1) := by
  classical
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  unfold finiteNumerator
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hrest : ∀ i j : ℕ, ¬ (N + 1 + 1) * (i + 1 + 1) + j ≤ N + 1 + 1 := by
    intro i j
    nlinarith
  simp only [hrest, ↓reduceIte, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.succ_eq_add_one, mul_one, mul_zero, zero_mul, zero_add, add_zero,
      pow_zero, pow_one, one_mul, qPochhammer_zero, qPochhammer_one, mul_one,
      quadraticExponent_zero, quadraticExponent_one, Nat.sub_self, Nat.sub_zero,
      gaussianBinomial_zero_right, le_refl, ↓reduceIte]
    unfold initialNumerator
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, qPochhammer_zero, mul_one]
    rw [add_comm]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (Nat.le_of_lt (Finset.mem_range.mp hj))]
    · simp only [numeratorCorrection, show N + 1 + 1 - (N + 1) = 1 by omega,
        gaussianBinomial_self]
      ring
  · intro j hj hj0
    have hbad : ¬ (N + 1 + 1) * 1 + j ≤ N + 1 + 1 := by omega
    rw [if_neg hbad]
  · simp

theorem finiteNumerator_eq_initial (N n : ℕ) (hN : 0 < N) (hn : n ≤ N + 1) :
    finiteNumerator N n = initialNumerator N (MvPowerSeries.X 0)
      (MvPowerSeries.X 1) (MvPowerSeries.X 2) n := by
  by_cases h : n ≤ N
  · exact finiteNumerator_eq_initial_of_le N n h
  · have he : n = N + 1 := by omega
    subst n
    exact finiteNumerator_eq_initial_boundary N hN

/-- The explicit numerator satisfies every short-range initial value,
including length N+1, in the multiplied form valid in ordinary power series. -/
theorem finiteNumerator_initial (N n : ℕ) (hN : 0 < N) (hn : n ≤ N) :
    (MvPowerSeries.X 2 : Series) * finiteNumerator N (n + 1) =
      (1 + MvPowerSeries.X 2) *
        qPochhammer (-MvPowerSeries.X 2 * (MvPowerSeries.X 0 : Series) ^ (N + 1) *
          MvPowerSeries.X 1) (MvPowerSeries.X 1) n -
        qPochhammer (-MvPowerSeries.X 2 * (MvPowerSeries.X 0 : Series) ^ N)
          (MvPowerSeries.X 1) (n + 1) := by
  rw [finiteNumerator_eq_initial N (n + 1) hN (by omega)]
  exact initialNumerator_multiplied _ _ _ _ _

end TorusLinkHomology.HilbertSeries
