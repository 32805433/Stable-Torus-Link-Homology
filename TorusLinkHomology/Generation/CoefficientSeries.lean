import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Euler operators with possibly noncommutative coefficients

The chain algebra is an exterior algebra, so its coefficients cannot be
assumed commutative. These coefficientwise operators apply to that algebra.
`shiftedEuler b` represents `x d/dx` on a bounded-above series
`x^b * f(x⁻¹)` using its power series of deficits `f`.
-/

noncomputable section

namespace TorusLinkHomology.CoefficientSeries

open scoped BigOperators

variable {A : Type*}

section Semiring

variable [Semiring A]

/-- The Euler operator on formal power series, over any coefficient semiring. -/
def euler (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => n • f.coeff n

@[simp] theorem coeff_euler (f : PowerSeries A) (n : ℕ) :
    (euler f).coeff n = n • f.coeff n :=
  PowerSeries.coeff_mk _ _

@[simp] theorem euler_zero : euler (0 : PowerSeries A) = 0 := by
  ext n
  simp

@[simp] theorem euler_add (f g : PowerSeries A) :
    euler (f + g) = euler f + euler g := by
  ext n
  simp [smul_add]

/-- Euler differentiation satisfies Leibniz without commuting any coefficients. -/
theorem euler_mul (f g : PowerSeries A) :
    euler (f * g) = euler f * g + f * euler g := by
  ext n
  simp only [coeff_euler, map_add, PowerSeries.coeff_mul, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have h := Finset.mem_antidiagonal.mp hij
  rw [← h, add_smul, smul_mul_assoc, mul_smul_comm]

@[simp] theorem euler_C (a : A) : euler (PowerSeries.C a) = 0 := by
  ext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

@[simp] theorem euler_one : euler (1 : PowerSeries A) = 0 := by
  simpa using euler_C (1 : A)

end Semiring

section Ring

variable [Ring A]

/-- Euler differentiation after reversing exponents around the upper bound `b`. -/
def shiftedEuler (b : ℤ) (f : PowerSeries A) : PowerSeries A :=
  b • f - euler f

@[simp] theorem coeff_shiftedEuler (b : ℤ) (f : PowerSeries A) (n : ℕ) :
    (shiftedEuler b f).coeff n = (b - (n : ℤ)) • f.coeff n := by
  simp only [shiftedEuler, map_sub, map_zsmul, coeff_euler, sub_smul,
    natCast_zsmul]

@[simp] theorem shiftedEuler_zero (b : ℤ) :
    shiftedEuler b (0 : PowerSeries A) = 0 := by
  simp [shiftedEuler]

theorem shiftedEuler_add (b : ℤ) (f g : PowerSeries A) :
    shiftedEuler b (f + g) = shiftedEuler b f + shiftedEuler b g := by
  simp only [shiftedEuler, smul_add, euler_add]
  abel

/-- Upper exponent bounds add under multiplication of reversed series. -/
theorem shiftedEuler_mul (b c : ℤ) (f g : PowerSeries A) :
    shiftedEuler (b + c) (f * g) =
      shiftedEuler b f * g + f * shiftedEuler c g := by
  simp only [shiftedEuler, euler_mul, add_smul, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm]
  abel

@[simp] theorem coeff_iterate_shiftedEuler (b : ℤ) (f : PowerSeries A) (j n : ℕ) :
    ((shiftedEuler b)^[j] f).coeff n = (b - (n : ℤ)) ^ j • f.coeff n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', coeff_shiftedEuler, ih, ← mul_smul, pow_succ']

variable {K : Type*} [CommRing K] [Algebra K A]

/-- Apply a scalar polynomial in the Euler operator to a reversed series. -/
def evalEuler (p : Polynomial K) (b : ℤ) (f : PowerSeries A) : PowerSeries A :=
  p.sum fun j a => a • ((shiftedEuler b)^[j] f)

/-- Each coefficient is an eigenvector for every polynomial in the Euler operator. -/
theorem coeff_evalEuler (p : Polynomial K) (b : ℤ) (f : PowerSeries A) (n : ℕ) :
    (evalEuler p b f).coeff n = p.eval ((b - (n : ℤ) : ℤ) : K) • f.coeff n := by
  classical
  simp only [evalEuler, Polynomial.sum_def, map_sum, PowerSeries.coeff_smul,
    coeff_iterate_shiftedEuler, Polynomial.eval_eq_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Int.cast_smul_eq_zsmul K, Int.cast_pow, smul_smul]

/-- A root of the selector polynomial removes the corresponding coefficient. -/
theorem coeff_evalEuler_eq_zero (p : Polynomial K) (b : ℤ) (f : PowerSeries A) (n : ℕ)
    (h : p.eval ((b - (n : ℤ) : ℤ) : K) = 0) :
    (evalEuler p b f).coeff n = 0 := by
  rw [coeff_evalEuler, h, zero_smul]

end Ring

end TorusLinkHomology.CoefficientSeries
