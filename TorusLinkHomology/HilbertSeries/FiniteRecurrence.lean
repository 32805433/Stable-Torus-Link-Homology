import TorusLinkHomology.HilbertSeries.FiniteNumerator

/-! Termwise recurrence for the finite numerator formula. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

variable {S : Type*} [CommRing S]

/-- The factor independent of length in a summand of the finite numerator. -/
def finiteWeight (N : ℕ) (s v z : S) (i j : ℕ) : S :=
  (-1) ^ i * s ^ (N * i) * v ^ (quadraticExponent N i + i * j) *
    qPochhammer s v i * qPochhammer (-z * s ^ N) v (N * i) *
    numeratorCorrection N (s * v ^ i) v z j

/-- A summand extended by zero beyond its length support. -/
def finiteTerm (N : ℕ) (s v z : S) (n i j : ℕ) : S :=
  if (N + 1) * i + j ≤ n then
    finiteWeight N s v z i j *
      qPochhammer (-z * s ^ (N + 1) * v ^ ((N + 1) * i + j)) v
        (n - ((N + 1) * i + j)) * gaussianBinomial v (n - N * i - j) i
  else 0

/-- The numerator with arbitrary values of its three parameters. -/
def finiteNumeratorAt (N n : ℕ) (s v z : S) : S :=
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (N + 1), finiteTerm N s v z n i j

theorem finiteNumerator_eq_at (N n : ℕ) :
    finiteNumerator N n = finiteNumeratorAt N n
      (MvPowerSeries.X 0) (MvPowerSeries.X 1) (MvPowerSeries.X 2) := rfl

/-- Shifting the outer summation index extracts precisely the correction
factor in the Hilbert recurrence. The slack l keeps all exponents natural. -/
theorem finiteWeight_shift (N i j l : ℕ) (s v z : S) :
    finiteWeight N s v z (i + 1) j * v ^ l =
      -((1 - s) * s ^ N * v ^ (N + (N + 1) * i + j + l) *
        qPochhammer (-z * s ^ N) v N) * finiteWeight N (s * v) v z i j := by
  unfold finiteWeight
  rw [qPochhammer_shift, show N * (i + 1) = N + N * i by ring,
    qPochhammer_add, quadraticExponent_succ]
  have hp : -z * (s * v) ^ N = (-z * s ^ N) * v ^ N := by rw [mul_pow]; ring
  have hd : s * v ^ (i + 1) = s * v * v ^ i := by rw [pow_succ']; ring
  rw [hp, hd]
  simp only [pow_add, mul_pow, pow_one]
  ring

theorem finiteTerm_at (N i j l : ℕ) (s v z : S) :
    finiteTerm N s v z ((N + 1) * i + j + l) i j =
      finiteWeight N s v z i j *
        qPochhammer (-z * s ^ (N + 1) * v ^ ((N + 1) * i + j)) v l *
        gaussianBinomial v (i + l) i := by
  have hupper : (N + 1) * i + j + l - N * i - j = i + l := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  simp only [finiteTerm, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left, hupper]

/-- The shifted parameters identify the two Pochhammer tails exactly. -/
theorem finiteTerm_shift_parameter (N i j : ℕ) (s v z : S) :
    -z * (s * v) ^ (N + 1) * v ^ ((N + 1) * i + j) =
      -z * s ^ (N + 1) * v ^ ((N + 1) * (i + 1) + j) := by
  simp only [Nat.mul_add, Nat.mul_one, pow_add, mul_pow]
  ring

/-- The term recurrence when the new length lies on or above its support. -/
theorem finiteTerm_step_at (N i j l : ℕ) (s v z : S) :
    finiteTerm N s v z (N + (N + 1) * i + j + l + 1) (i + 1) j =
      (1 + z * s ^ (N + 1) * v ^ (N + (N + 1) * i + j + l)) *
        finiteTerm N s v z (N + (N + 1) * i + j + l) (i + 1) j -
      ((1 - s) * s ^ N * v ^ (N + (N + 1) * i + j + l) *
        qPochhammer (-z * s ^ N) v N) *
        finiteTerm N (s * v) v z ((N + 1) * i + j + l) i j := by
  have hnew : N + (N + 1) * i + j + l + 1 = (N + 1) * (i + 1) + j + l := by ring
  rw [hnew, finiteTerm_at, finiteTerm_at, finiteTerm_shift_parameter]
  have hw := finiteWeight_shift N i j l s v z
  cases l with
  | zero =>
    have hbad : ¬ (N + 1) * (i + 1) + j ≤ N + (N + 1) * i + j + 0 := by
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    rw [finiteTerm, if_neg hbad]
    simp only [add_zero, qPochhammer_zero, mul_one, gaussianBinomial_self, pow_zero,
      mul_zero, zero_sub] at hw ⊢
    rw [hw]
    ring
  | succ l =>
    have hold : N + (N + 1) * i + j + (l + 1) = (N + 1) * (i + 1) + j + l := by ring
    rw [hold, finiteTerm_at, qPochhammer_succ]
    have hp : (-z * s ^ (N + 1) * v ^ ((N + 1) * (i + 1) + j)) * v ^ l =
        -z * s ^ (N + 1) * v ^ (N + (N + 1) * i + j + (l + 1)) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      ring
    rw [hp]
    rw [show (i + 1) + (l + 1) = (i + l + 1) + 1 by omega, gaussianBinomial]
    rw [show i + l + 1 - i = l + 1 by omega]
    simp only [show i + 1 + l = i + l + 1 by omega,
      show i + (l + 1) = i + l + 1 by omega]
    linear_combination
      qPochhammer (-z * s ^ (N + 1) * v ^ ((N + 1) * (i + 1) + j)) v l *
        (1 + z * s ^ (N + 1) * v ^ (N + (N + 1) * i + j + (l + 1))) *
        gaussianBinomial v (i + l + 1) i * hw

theorem finiteTerm_step (N n i j : ℕ) (hn : N ≤ n) (s v z : S) :
    finiteTerm N s v z (n + 1) (i + 1) j =
      (1 + z * s ^ (N + 1) * v ^ n) * finiteTerm N s v z n (i + 1) j -
      ((1 - s) * s ^ N * v ^ n * qPochhammer (-z * s ^ N) v N) *
        finiteTerm N (s * v) v z (n - N) i j := by
  by_cases hs : (N + 1) * (i + 1) + j ≤ n + 1
  · let l := n + 1 - ((N + 1) * (i + 1) + j)
    have he : n = N + (N + 1) * i + j + l := by
      dsimp [l]
      simp only [Nat.mul_add, Nat.mul_one] at hs ⊢
      omega
    have he' : n - N = (N + 1) * i + j + l := by omega
    rw [he']
    conv_lhs => rw [he]
    conv_rhs => rw [he]
    exact finiteTerm_step_at N i j l s v z
  · have hs' : ¬ (N + 1) * (i + 1) + j ≤ n := by omega
    have ht : ¬ (N + 1) * i + j ≤ n - N := by
      simp only [Nat.mul_add, Nat.mul_one] at hs
      omega
    simp only [finiteTerm, if_neg hs, if_neg hs', if_neg ht, mul_zero, sub_zero]

theorem finiteTerm_step_zero (N n j : ℕ) (hj : j ≤ n) (s v z : S) :
    finiteTerm N s v z (n + 1) 0 j =
      (1 + z * s ^ (N + 1) * v ^ n) * finiteTerm N s v z n 0 j := by
  have hj' : j ≤ n + 1 := by omega
  simp only [finiteTerm, mul_zero, zero_add, if_pos hj, if_pos hj', Nat.sub_zero,
    gaussianBinomial_zero_right, mul_one]
  rw [show n + 1 - j = (n - j) + 1 by omega, qPochhammer_succ]
  have he : (-z * s ^ (N + 1) * v ^ j) * v ^ (n - j) =
      -z * s ^ (N + 1) * v ^ n := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hj]
  rw [he]
  ring

/-- Extending the outer summation bound adds only unsupported zero terms. -/
theorem finiteNumeratorAt_eq_sum (N n m : ℕ) (hm : n + 1 ≤ m) (s v z : S) :
    finiteNumeratorAt N n s v z =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range (N + 1), finiteTerm N s v z n i j := by
  unfold finiteNumeratorAt
  apply Finset.sum_subset (Finset.range_mono hm)
  intro i hi hin
  have hni : n < i := by simpa using hin
  apply Finset.sum_eq_zero
  intro j hj
  have hbad : ¬ (N + 1) * i + j ≤ n := by nlinarith
  simp only [finiteTerm, if_neg hbad]

/-- The explicit finite sum satisfies the Hilbert numerator recurrence. -/
theorem finiteNumeratorAt_recurrence (N n : ℕ) (hn : N ≤ n) (s v z : S) :
    finiteNumeratorAt N (n + 1) s v z =
      (1 + z * s ^ (N + 1) * v ^ n) * finiteNumeratorAt N n s v z -
      ((1 - s) * s ^ N * v ^ n * qPochhammer (-z * s ^ N) v N) *
        finiteNumeratorAt N (n - N) (s * v) v z := by
  rw [finiteNumeratorAt_eq_sum N n (n + 2) (by omega),
    finiteNumeratorAt_eq_sum N (n - N) (n + 1) (by omega)]
  unfold finiteNumeratorAt
  rw [Finset.sum_range_succ']
  conv_rhs => lhs; rhs; rw [Finset.sum_range_succ']
  have hzero : (∑ j ∈ Finset.range (N + 1), finiteTerm N s v z (n + 1) 0 j) =
      (1 + z * s ^ (N + 1) * v ^ n) *
        ∑ j ∈ Finset.range (N + 1), finiteTerm N s v z n 0 j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact finiteTerm_step_zero N n j (by have := Finset.mem_range.mp hj; omega) s v z
  rw [hzero]
  simp only [finiteTerm_step N n _ _ hn, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Specialization of the proved recurrence to the public numerator. -/
theorem finiteNumerator_recurrence (N n : ℕ) (hn : N ≤ n) :
    finiteNumerator N (n + 1) =
      (1 + MvPowerSeries.X 2 * (MvPowerSeries.X 0 : Series) ^ (N + 1) *
        MvPowerSeries.X 1 ^ n) * finiteNumerator N n -
      ((1 - MvPowerSeries.X 0) * (MvPowerSeries.X 0 : Series) ^ N * MvPowerSeries.X 1 ^ n *
        qPochhammer (-MvPowerSeries.X 2 * MvPowerSeries.X 0 ^ N) (MvPowerSeries.X 1) N) *
        finiteNumeratorAt N (n - N) (MvPowerSeries.X 0 * MvPowerSeries.X 1)
          (MvPowerSeries.X 1) (MvPowerSeries.X 2) := by
  simp only [finiteNumerator_eq_at]
  exact finiteNumeratorAt_recurrence N n hn _ _ _

theorem map_gaussianBinomial {T : Type*} [CommRing T] (f : S →+* T) (v : S) (n k : ℕ) :
    f (gaussianBinomial v n k) = gaussianBinomial (f v) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [gaussianBinomial]
  | succ n ih => cases k <;> simp [gaussianBinomial, ih]

theorem map_numeratorCorrection {T : Type*} [CommRing T] (f : S →+* T)
    (N : ℕ) (s v z : S) (j : ℕ) :
    f (numeratorCorrection N s v z j) = numeratorCorrection N (f s) (f v) (f z) j := by
  cases j with
  | zero => simp [numeratorCorrection]
  | succ j =>
    cases j <;> simp [numeratorCorrection, map_qPochhammer]

/-- Polynomial naturality gives compatibility with the s ↦ sv substitution. -/
theorem map_finiteNumeratorAt {T : Type*} [CommRing T] (f : S →+* T)
    (N n : ℕ) (s v z : S) :
    f (finiteNumeratorAt N n s v z) = finiteNumeratorAt N n (f s) (f v) (f z) := by
  simp only [finiteNumeratorAt, finiteTerm, finiteWeight, map_sum, apply_ite, map_zero,
    map_mul, map_pow, map_neg, map_one, map_qPochhammer, map_numeratorCorrection,
    map_gaussianBinomial]

/-- Initial values through N determine a sequence satisfying the shifted
Hilbert numerator recurrence. -/
theorem numerator_recurrence_unique (N : ℕ) (shift : S →+* S)
    (factor correction f g : ℕ → S)
    (hinit : ∀ n ≤ N, f n = g n)
    (hf : ∀ n, N ≤ n → f (n + 1) = factor n * f n - correction n * shift (f (n - N)))
    (hg : ∀ n, N ≤ n → g (n + 1) = factor n * g n - correction n * shift (g (n - N))) :
    f = g := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ N
    · exact hinit n hn
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have hNn : N ≤ n := by omega
      rw [hf n hNn, hg n hNn, ih n (by omega), ih (n - N) (by omega)]

end TorusLinkHomology.HilbertSeries
