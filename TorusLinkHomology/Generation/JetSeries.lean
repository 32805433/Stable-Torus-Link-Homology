import TorusLinkHomology.Generation.CoefficientSeries
import DGA.PowerSeriesAlgebra
import Mathlib.RingTheory.PowerSeries.Exp

/-! # Divided Euler jets of coefficient series

The upper exponent is recorded explicitly. Multiplication adds upper bounds,
so the formulas apply to bounded-above series of exterior coefficients.
-/

noncomputable section

namespace TorusLinkHomology.CoefficientSeries

open scoped BigOperators

theorem dividedPower_add (a b : ℚ) (k : ℕ) :
    (a + b) ^ k / (k.factorial : ℚ) =
      ∑ ij ∈ Finset.antidiagonal k,
        (a ^ ij.1 / (ij.1.factorial : ℚ)) * (b ^ ij.2 / (ij.2.factorial : ℚ)) := by
  have h := congrArg (PowerSeries.coeff k) (PowerSeries.exp_mul_exp_eq_exp_add a b)
  simpa only [PowerSeries.coeff_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    Algebra.algebraMap_self, RingHom.id_apply, div_eq_mul_inv, one_mul] using h.symm

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The k-th Euler jet, divided by k!, at upper exponent b. -/
def hasseEuler (b : ℤ) (k : ℕ) (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun t => (((b - (t : ℤ) : ℤ) : ℚ) ^ k / (k.factorial : ℚ)) • f.coeff t

@[simp] theorem coeff_hasseEuler (b : ℤ) (k : ℕ) (f : PowerSeries A) (t : ℕ) :
    (hasseEuler b k f).coeff t =
      (((b - (t : ℤ) : ℤ) : ℚ) ^ k / (k.factorial : ℚ)) • f.coeff t :=
  PowerSeries.coeff_mk _ _

theorem hasseEuler_eq_iterate (b : ℤ) (k : ℕ) (f : PowerSeries A) :
    hasseEuler b k f = ((k.factorial : ℚ)⁻¹) • (shiftedEuler b)^[k] f := by
  ext t : 1
  simp only [coeff_hasseEuler, PowerSeries.coeff_smul, coeff_iterate_shiftedEuler,
    ← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, smul_smul, div_eq_mul_inv, mul_comm]

@[simp] theorem hasseEuler_zero (b : ℤ) (f : PowerSeries A) : hasseEuler b 0 f = f := by
  ext t : 1
  simp

/-- Divided Euler differentiation satisfies the convolution Leibniz rule
without commuting the chain coefficients. -/
theorem hasseEuler_mul (b c : ℤ) (k : ℕ) (f g : PowerSeries A) :
    hasseEuler (b + c) k (f * g) =
      ∑ ij ∈ Finset.antidiagonal k,
        hasseEuler b ij.1 f * hasseEuler c ij.2 g := by
  ext t : 1
  simp only [coeff_hasseEuler, map_sum, PowerSeries.coeff_mul, coeff_hasseEuler,
    smul_mul_assoc, mul_smul_comm, smul_smul, Finset.smul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [← Finset.sum_smul]
  congr 1
  have hab' := Finset.mem_antidiagonal.mp hab
  have hsplit : b + c - (t : ℤ) = (b - (ab.1 : ℤ)) + (c - (ab.2 : ℤ)) := by omega
  rw [hsplit, Int.cast_add]
  simpa only [mul_comm] using dividedPower_add
    (((b - (ab.1 : ℤ) : ℤ) : ℚ)) (((c - (ab.2 : ℤ) : ℤ) : ℚ)) k

/-- The first `n` divided Euler jets, in a separate polynomial variable. -/
def jetPolynomial (n : ℕ) (b : ℤ) (f : PowerSeries A) : Polynomial (PowerSeries A) :=
  ∑ j : Fin n, Polynomial.monomial j.val (hasseEuler b j.val f)

/-- Truncation preserves every jet below the cutoff. -/
theorem coeff_jetPolynomial_of_lt (n : ℕ) (b : ℤ) (f : PowerSeries A)
    (j : ℕ) (hj : j < n) :
    (jetPolynomial n b f).coeff j = hasseEuler b j f := by
  classical
  simp only [jetPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]
  · simp
  · intro i _ hi
    apply if_neg
    exact fun h => hi (Fin.ext h)
  · simp

/-- Beyond the finite cutoff, the jet polynomial has no coefficients. -/
theorem coeff_jetPolynomial_of_le (n : ℕ) (b : ℤ) (f : PowerSeries A)
    (j : ℕ) (hj : n ≤ j) : (jetPolynomial n b f).coeff j = 0 := by
  classical
  simp only [jetPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (by have := i.isLt; omega)

/-- Constant one at upper exponent zero has just its zeroth jet. -/
theorem hasseEuler_one (j : ℕ) :
    hasseEuler 0 j (1 : PowerSeries A) = if j = 0 then 1 else 0 := by
  ext t : 1
  by_cases ht : t = 0
  · subst t
    cases j <;> simp
  · by_cases hj : j = 0 <;> simp [PowerSeries.coeff_one, ht, hj]

/-- The coefficient of a power below the jet cutoff is the corresponding
divided Euler derivative of the power. This uses the convolution Leibniz
rule and is valid for noncommutative coefficient algebras. -/
theorem coeff_jetPolynomial_pow_of_lt (n N : ℕ) (b : ℤ) (f : PowerSeries A)
    (j : ℕ) (hj : j < n) :
    ((jetPolynomial n b f) ^ N).coeff j = hasseEuler ((N : ℤ) * b) j (f ^ N) := by
  induction N generalizing j with
  | zero => simp [hasseEuler_one, Polynomial.coeff_one]
  | succ N ih =>
    rw [pow_succ, Polynomial.coeff_mul]
    have hbound : ((N + 1 : ℕ) : ℤ) * b = (N : ℤ) * b + b := by push_cast; ring
    rw [hbound, pow_succ, hasseEuler_mul]
    apply Finset.sum_congr rfl
    intro ab hab
    have hab' := Finset.mem_antidiagonal.mp hab
    rw [ih ab.1 (by omega), coeff_jetPolynomial_of_lt n b f ab.2 (by omega)]

/-- Ordinary Euler derivatives are factorial times divided Euler jets. -/
theorem factorial_smul_hasseEuler (b : ℤ) (k : ℕ) (f : PowerSeries A) :
    (k.factorial : ℚ) • hasseEuler b k f = (shiftedEuler b)^[k] f := by
  rw [hasseEuler_eq_iterate, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero), one_smul]

/-- Multiplication by the natural factorial gives the same normalization. -/
theorem factorial_mul_hasseEuler (b : ℤ) (k : ℕ) (f : PowerSeries A) :
    (k.factorial : PowerSeries A) * hasseEuler b k f = (shiftedEuler b)^[k] f := by
  simpa only [Algebra.smul_def, map_natCast] using factorial_smul_hasseEuler b k f

@[simp] theorem hasseEuler_add (b : ℤ) (k : ℕ) (f g : PowerSeries A) :
    hasseEuler b k (f + g) = hasseEuler b k f + hasseEuler b k g := by
  ext t : 1
  simp only [coeff_hasseEuler, map_add, smul_add]

@[simp] theorem hasseEuler_sub (b : ℤ) (k : ℕ) (f g : PowerSeries A) :
    hasseEuler b k (f - g) = hasseEuler b k f - hasseEuler b k g := by
  ext t : 1
  simp only [coeff_hasseEuler, map_sub, smul_sub]

@[simp] theorem hasseEuler_smul (b : ℤ) (k : ℕ) (a : ℚ) (f : PowerSeries A) :
    hasseEuler b k (a • f) = a • hasseEuler b k f := by
  ext t : 1
  simp only [coeff_hasseEuler, PowerSeries.coeff_smul]
  exact smul_comm _ _ _

end TorusLinkHomology.CoefficientSeries
