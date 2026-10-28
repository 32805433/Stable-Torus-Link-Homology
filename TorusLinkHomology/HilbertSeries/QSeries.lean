import TorusLinkHomology.HilbertSeries.Definitions
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Finite product identities used in the Hilbert numerator and Gordon sums. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

variable {S : Type*} [CommRing S]

@[simp] theorem qPochhammer_zero (a v : S) : qPochhammer a v 0 = 1 := by
  simp [qPochhammer]

@[simp] theorem qPochhammer_succ (a v : S) (m : ℕ) :
    qPochhammer a v (m + 1) = qPochhammer a v m * (1 - a * v ^ m) := by
  simp [qPochhammer, Finset.prod_range_succ]

@[simp] theorem qPochhammer_one (a v : S) : qPochhammer a v 1 = 1 - a := by
  simp

theorem qPochhammer_add (a v : S) (m n : ℕ) :
    qPochhammer a v (m + n) = qPochhammer a v m * qPochhammer (a * v ^ m) v n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Nat.add_assoc, qPochhammer_succ, ih, qPochhammer_succ, mul_assoc,
      pow_add, mul_assoc]

theorem qPochhammer_shift (a v : S) (m : ℕ) :
    qPochhammer a v (m + 1) = (1 - a) * qPochhammer (a * v) v m := by
  simpa [Nat.add_comm] using qPochhammer_add a v 1 m

@[simp] theorem gaussianBinomial_zero_right (v : S) (n : ℕ) :
    gaussianBinomial v n 0 = 1 := by cases n <;> rfl

theorem gaussianBinomial_eq_zero (v : S) {n k : ℕ} (h : n < k) :
    gaussianBinomial v n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> simp_all [gaussianBinomial]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      rw [gaussianBinomial, ih (by omega), ih (by omega), mul_zero, add_zero]

@[simp] theorem gaussianBinomial_self (v : S) (n : ℕ) :
    gaussianBinomial v n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gaussianBinomial, gaussianBinomial_eq_zero v (Nat.lt_succ_self n), ih]

/-- A product with parameter of zero constant coefficient is invertible. -/
theorem constantCoeff_qPochhammer {σ : Type*} (a v : MvPowerSeries σ ℚ)
    (ha : MvPowerSeries.constantCoeff a = 0) (m : ℕ) :
    MvPowerSeries.constantCoeff (qPochhammer a v m) = 1 := by
  induction m with
  | zero => simp
  | succ m ih => simp [ih, ha]

theorem qPochhammer_mul_inv {σ : Type*} (a v : MvPowerSeries σ ℚ)
    (ha : MvPowerSeries.constantCoeff a = 0) (m : ℕ) :
    qPochhammer a v m * (qPochhammer a v m)⁻¹ = 1 := by
  apply MvPowerSeries.mul_inv_cancel
  rw [constantCoeff_qPochhammer a v ha m]
  exact one_ne_zero

/-- The denominator cancellation used for positive successive differences in
Gordon sums, stated with a successor so no truncated subtraction is needed. -/
theorem qPochhammer_inv_step {σ : Type*} (v : MvPowerSeries σ ℚ)
    (hv : MvPowerSeries.constantCoeff v = 0) (m : ℕ) :
    (1 - v ^ (m + 1)) * (qPochhammer v v (m + 1))⁻¹ =
      (qPochhammer v v m)⁻¹ := by
  apply (MvPowerSeries.eq_inv_iff_mul_eq_one (by
    rw [constantCoeff_qPochhammer v v hv m]; exact one_ne_zero)).2
  calc
    (1 - v ^ (m + 1)) * (qPochhammer v v (m + 1))⁻¹ * qPochhammer v v m =
        qPochhammer v v (m + 1) * (qPochhammer v v (m + 1))⁻¹ := by
      rw [qPochhammer_succ, pow_succ']; ring
    _ = 1 := qPochhammer_mul_inv v v hv _

/-- Finite Pochhammer products commute with coefficient homomorphisms. -/
theorem map_qPochhammer {T : Type*} [CommRing T] (f : S →+* T) (a v : S) (m : ℕ) :
    f (qPochhammer a v m) = qPochhammer (f a) (f v) m := by
  simp [qPochhammer]

/-- Length series whose coefficients are Gaussian binomials. -/
def gaussianLengthSeries (v : S) (i : ℕ) : PowerSeries S :=
  PowerSeries.mk (fun m => gaussianBinomial v (m + i) i)

@[simp] theorem coeff_gaussianLengthSeries (v : S) (i m : ℕ) :
    PowerSeries.coeff m (gaussianLengthSeries v i) = gaussianBinomial v (m + i) i :=
  PowerSeries.coeff_mk _ _

private theorem rescale_C (v c : S) :
    PowerSeries.rescale v (PowerSeries.C c) = PowerSeries.C c := by
  ext m
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with hm <;> simp [hm]

/-- The defining Gaussian recurrence is a functional equation in length. -/
theorem gaussianLengthSeries_step (v : S) (i : ℕ) :
    (1 - PowerSeries.X) * gaussianLengthSeries v (i + 1) =
      PowerSeries.rescale v (gaussianLengthSeries v i) := by
  ext m
  rw [sub_mul, one_mul, map_sub]
  cases m with
  | zero => simp [PowerSeries.coeff_rescale]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, coeff_gaussianLengthSeries,
      coeff_gaussianLengthSeries, PowerSeries.coeff_rescale, coeff_gaussianLengthSeries]
    rw [show m + 1 + (i + 1) = (m + i + 1) + 1 by omega, gaussianBinomial]
    simp only [show m + i + 1 - i = m + 1 by omega,
      show m + (i + 1) = m + i + 1 by omega,
      show m + 1 + i = m + i + 1 by omega]
    ring

private theorem gaussianLengthSeries_zero_mul (v : S) :
    (1 - PowerSeries.X) * gaussianLengthSeries v 0 = 1 := by
  ext m
  rw [sub_mul, one_mul, map_sub]
  cases m with
  | zero => simp
  | succ m => simp [PowerSeries.coeff_succ_X_mul]

/-- Multiplying the Gaussian length series by its finite denominator gives one.
This holds over any commutative coefficient ring, including `Series`. -/
theorem qPochhammer_mul_gaussianLengthSeries (v : S) (i : ℕ) :
    qPochhammer PowerSeries.X (PowerSeries.C v) (i + 1) *
      gaussianLengthSeries v i = 1 := by
  induction i with
  | zero => simpa using gaussianLengthSeries_zero_mul v
  | succ i ih =>
    rw [qPochhammer_shift]
    calc
      (1 - PowerSeries.X) *
          qPochhammer (PowerSeries.X * PowerSeries.C v) (PowerSeries.C v) (i + 1) *
          gaussianLengthSeries v (i + 1) =
        qPochhammer (PowerSeries.X * PowerSeries.C v) (PowerSeries.C v) (i + 1) *
          ((1 - PowerSeries.X) * gaussianLengthSeries v (i + 1)) := by ring
      _ = PowerSeries.rescale v
          (qPochhammer PowerSeries.X (PowerSeries.C v) (i + 1) *
            gaussianLengthSeries v i) := by
        rw [gaussianLengthSeries_step, map_mul, map_qPochhammer, PowerSeries.rescale_X, rescale_C]
        congr 2
        exact mul_comm _ _
      _ = 1 := by rw [ih, map_one]

theorem constantCoeff_lengthPochhammer (v : S) (i : ℕ) :
    PowerSeries.constantCoeff (qPochhammer PowerSeries.X (PowerSeries.C v) i) = 1 := by
  induction i with
  | zero => simp
  | succ i ih => simp [ih]

/-- The coefficient identity for the inverse finite Pochhammer product. The
unit inverse is used because the coefficient ring need not be a field. -/
theorem coeff_invOfUnit_qPochhammer (v : S) (i m : ℕ) :
    PowerSeries.coeff m
      (PowerSeries.invOfUnit (qPochhammer PowerSeries.X (PowerSeries.C v) (i + 1)) 1) =
      gaussianBinomial v (m + i) i := by
  have hi := PowerSeries.invOfUnit_mul
    (qPochhammer PowerSeries.X (PowerSeries.C v) (i + 1)) 1
    (constantCoeff_lengthPochhammer v (i + 1))
  have he : PowerSeries.invOfUnit (qPochhammer PowerSeries.X (PowerSeries.C v) (i + 1)) 1 =
      gaussianLengthSeries v i := by
    calc
      _ = PowerSeries.invOfUnit (qPochhammer PowerSeries.X (PowerSeries.C v) (i + 1)) 1 *
          (qPochhammer PowerSeries.X (PowerSeries.C v) (i + 1) * gaussianLengthSeries v i) := by
        rw [qPochhammer_mul_gaussianLengthSeries, mul_one]
      _ = _ := by rw [← mul_assoc, hi, one_mul]
  rw [he, coeff_gaussianLengthSeries]

@[simp] theorem quadraticExponent_zero (N : ℕ) : quadraticExponent N 0 = 0 := by
  simp [quadraticExponent]

/-- Integral first differences of the quadratic exponent, avoiding division
and subtraction in subsequent index shifts. -/
theorem quadraticExponent_succ (N j : ℕ) :
    quadraticExponent N (j + 1) = quadraticExponent N j + (2 * N + 1) * j + N := by
  have hj : j ≤ (2 * N + 1) * j ^ 2 := by
    nlinarith [Nat.zero_le (N * j ^ 2)]
  have hj' : j + 1 ≤ (2 * N + 1) * (j + 1) ^ 2 := by
    nlinarith [Nat.zero_le (N * (j + 1) ^ 2)]
  have he : (2 * N + 1) * (j + 1) ^ 2 - (j + 1) =
      ((2 * N + 1) * j ^ 2 - j) + 2 * ((2 * N + 1) * j + N) := by
    have h1 := Nat.sub_add_cancel hj
    have h2 := Nat.sub_add_cancel hj'
    nlinarith
  unfold quadraticExponent
  rw [he]
  omega

@[simp] theorem quadraticExponent_one (N : ℕ) : quadraticExponent N 1 = N := by
  simpa using quadraticExponent_succ N 0

/-- The quadratic factor absorbs every potentially negative Gordon exponent. -/
theorem quadraticExponent_ge_linear (N j : ℕ) : N * j ≤ quadraticExponent N j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [quadraticExponent_succ, Nat.mul_add, Nat.mul_one]
    omega

theorem quadraticExponent_ge_gordon_shift (N i j : ℕ) (hi : i ≤ N) :
    (i - 1) * j ≤ quadraticExponent N j :=
  (Nat.mul_le_mul_right j (by omega)).trans (quadraticExponent_ge_linear N j)

/-- The finite q-binomial theorem, coefficientwise and without division. -/
theorem coeff_qPochhammer_neg_X (v : S) (n m : ℕ) :
    PowerSeries.coeff m (qPochhammer (-PowerSeries.X) (PowerSeries.C v) n) =
      v ^ quadraticExponent 0 m * gaussianBinomial v n m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp
    | succ m => simp [gaussianBinomial]
  | succ n ih =>
    rw [qPochhammer_succ]
    have he : (1 - (-PowerSeries.X : PowerSeries S) * PowerSeries.C v ^ n) =
        1 + PowerSeries.C (v ^ n) * PowerSeries.X := by
      rw [map_pow]; ring
    rw [he, mul_add, mul_one, map_add]
    cases m with
    | zero => simp [ih]
    | succ m =>
      have hcoeff : PowerSeries.coeff (m + 1)
          (qPochhammer (-PowerSeries.X) (PowerSeries.C v) n *
            (PowerSeries.C (v ^ n) * PowerSeries.X)) =
          v ^ n * PowerSeries.coeff m (qPochhammer (-PowerSeries.X) (PowerSeries.C v) n) := by
        rw [← mul_assoc, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
        exact mul_comm _ _
      rw [hcoeff, ih, ih, gaussianBinomial]
      by_cases hm : m ≤ n
      · have hexp : quadraticExponent 0 (m + 1) + (n - m) =
            n + quadraticExponent 0 m := by
          rw [quadraticExponent_succ]
          simp only [mul_zero, zero_add, one_mul, add_zero]
          omega
        rw [mul_add, ← mul_assoc (v ^ quadraticExponent 0 (m + 1)), ← pow_add, hexp, pow_add]
        ring
      · have hnm : n < m := Nat.lt_of_not_ge hm
        rw [gaussianBinomial_eq_zero v hnm, mul_zero, mul_zero, add_zero]
        ring

/-- A sufficiently steep positive specialization separates a fixed supported
bidegree from every other bidegree in the same support cone. -/
theorem specialization_degree_separation {C r a b a' b' : ℕ}
    (hb : b ≤ C * a) (hb' : b' ≤ C * a') (hr : C * (a + 1) < r)
    (he : r * a - b = r * a' - b') : a = a' ∧ b = b' := by
  have hCr : C < r := by nlinarith
  have hba : b ≤ r * a := hb.trans (Nat.mul_le_mul_right a (Nat.le_of_lt hCr))
  have hba' : b' ≤ r * a' := hb'.trans (Nat.mul_le_mul_right a' (Nat.le_of_lt hCr))
  have he' : r * a + b' = r * a' + b := by omega
  have haa' : a = a' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hgap : a + 1 ≤ a' := hlt
      have hpos : (r - C) * (a + 1) ≤ (r - C) * a' := Nat.mul_le_mul_left _ hgap
      have hdiff : r - C + C = r := Nat.sub_add_cancel (Nat.le_of_lt hCr)
      nlinarith
    · have hgap : a' + 1 ≤ a := hgt
      nlinarith
  exact ⟨haa', by subst a'; omega⟩

end TorusLinkHomology.HilbertSeries
