import TorusLinkHomology.Generation.CoefficientComplex
import TorusLinkHomology.Generation.CoefficientSeries

/-!
# Actual tail-series identities

ET-01/02 are implemented coefficientwise. Multiplication by the polynomial
`E` involves only finitely many summands at each coefficient. The support
bound below constructs an actual polynomial for `C`; the full series `X` and
`W` need not be polynomials.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientComplex
namespace TailSeries

variable {M : Type*} [AddCommGroup M]

/-- The coefficient operator of `E DY - N (DE)Y`. Negative source indices
are omitted explicitly. This acts on arbitrary sequences with module coefficients. -/
def eulerOperator (N r : ℕ) [Module (R r) M] : (ℕ → M) →ₗ[R r] (ℕ → M) :=
  LinearMap.pi fun j => (j : R r) • LinearMap.proj j +
    ∑ i : Fin r, if i.val + 1 ≤ j then
      (((j : R r) - ((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r)) * e r i) •
        LinearMap.proj (j - (i.val + 1)) else 0

@[simp] theorem eulerOperator_apply (N r : ℕ) [Module (R r) M] (Y : ℕ → M) (j : ℕ) :
    eulerOperator N r Y j = (j : R r) • Y j +
      ∑ i : Fin r, if i.val + 1 ≤ j then
        (((j : R r) - ((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r)) * e r i) •
          Y (j - (i.val + 1)) else 0 := by
  classical
  simp only [eulerOperator, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, LinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Every coefficient is a finite combination of coefficients of the input. -/
theorem eulerOperator_mem (N r : ℕ) [Module (R r) M] (S : Submodule (R r) M)
    (Y : ℕ → M) (hY : ∀ j, Y j ∈ S) (j : ℕ) : eulerOperator N r Y j ∈ S := by
  rw [eulerOperator_apply]
  apply S.add_mem (S.smul_mem _ (hY j))
  apply S.sum_mem
  intro i _
  split_ifs
  · exact S.smul_mem _ (hY _)
  · exact S.zero_mem

/-- A polynomial of degree at most `b` is sent to one of degree at most `b+r`. -/
theorem eulerOperator_support (N r b : ℕ) [Module (R r) M] (Y : ℕ → M)
    (hY : ∀ j, b < j → Y j = 0) (j : ℕ) (hj : b + r < j) :
    eulerOperator N r Y j = 0 := by
  rw [eulerOperator_apply, hY j (by omega), smul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs
  · rw [hY _ (by have := i.isLt; omega), smul_zero]
  · rfl

/-- Any coefficient-linear map commutes with the Euler coefficient operator. -/
theorem map_eulerOperator {M' : Type*} [AddCommGroup M'] (N r : ℕ)
    [Module (R r) M] [Module (R r) M'] (f : M →ₗ[R r] M') (Y : ℕ → M) (j : ℕ) :
    f (eulerOperator N r Y j) = eulerOperator N r (fun k => f (Y k)) j := by
  classical
  simp only [eulerOperator_apply, map_add, map_smul, map_sum, apply_ite, map_zero]

/-- The actual infinite tail series `X`. Its coefficients below the offset vanish. -/
def X (N r ell : ℕ) : ℕ → A r := tail N r ell

/-- The polynomial part `C = -X_{≤Nr}`. -/
def C (N r ell : ℕ) (j : ℕ) : A r :=
  if j ≤ N * r then -X N r ell j else 0

/-- The positive tail `W = -X_{>Nr}`. -/
def W (N r ell : ℕ) (j : ℕ) : A r :=
  if N * r < j then -X N r ell j else 0

/-- Coefficients of `Q = -N⁻¹ S_E(X)`. -/
def Q (N r ell : ℕ) : ℕ → A r :=
  -(invNat r N) • eulerOperator N r (X N r ell)

/-- Coefficients of `P = NQ-S_E(C)`. -/
def P (N r ell : ℕ) : ℕ → A r :=
  (N : R r) • Q N r ell - eulerOperator N r (C N r ell)

theorem C_add_W (N r ell : ℕ) : C N r ell + W N r ell = -X N r ell := by
  funext j
  by_cases hj : j ≤ N * r <;> simp [C, W, hj, lt_iff_not_ge]

theorem d_W (N r ell j : ℕ) (hell : ell ≤ N * r) : d N r ell (W N r ell j) = 0 := by
  by_cases hj : N * r < j
  · rw [W, if_pos hj, map_neg, X, tail_is_cycle _ _ _ _ (by omega) hj, neg_zero]
  · rw [W, if_neg hj, map_zero]

/-- The extended-tail recurrence cancels every coefficient above `ell+r`. -/
theorem eulerOperator_X_eq_zero (N r ell j : ℕ) (hj : ell + r < j) :
    eulerOperator N r (X N r ell) j = 0 := by
  rw [eulerOperator_apply, X, tail_recurrence _ _ _ _ hj]
  have hterm (i : Fin r) :
      (if i.val + 1 ≤ j then
        (((j : R r) - ((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r)) * e r i) •
          tail N r ell (j - (i.val + 1)) else 0) =
      -(((((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) * e r i) •
          tail N r ell (j - (i.val + 1))) := by
    rw [if_pos (by have := i.isLt; omega), ← neg_smul]
    congr 1
    ring
  simp only [hterm, Finset.sum_neg_distrib, add_neg_cancel]

/-- Thus `Q` is a polynomial, rather than an arbitrary tail series. -/
theorem Q_support (N r ell j : ℕ) (hj : ell + r < j) : Q N r ell j = 0 := by
  simp only [Q, Pi.smul_apply, eulerOperator_X_eq_zero _ _ _ _ hj, smul_zero]

/-- Multiplication by `N` clears the rational scalar used in `Q`. -/
theorem nat_smul_Q (N r ell : ℕ) (hN : 0 < N) :
    (N : R r) • Q N r ell = -eulerOperator N r (X N r ell) := by
  rw [Q, smul_smul, mul_neg, nat_mul_invNat r N hN, neg_smul, one_smul]

/-- ET-02's strict identity `P=S_E(W)`, before passing to homology. -/
theorem P_eq_eulerOperator_W (N r ell : ℕ) (hN : 0 < N) :
    P N r ell = eulerOperator N r (W N r ell) := by
  have h := congrArg (eulerOperator N r) (C_add_W N r ell)
  rw [map_add, map_neg] at h
  rw [P, nat_smul_Q _ _ _ hN, ← h, add_sub_cancel_left]

/-- Every coefficient of `P` is closed. -/
theorem d_P (N r ell j : ℕ) (hN : 0 < N) (hell : ell ≤ N * r) :
    d N r ell (P N r ell j) = 0 := by
  rw [P_eq_eulerOperator_W _ _ _ hN, map_eulerOperator]
  have hW : (fun k => d N r ell (W N r ell k)) = 0 := by
    funext k
    exact d_W N r ell k hell
  rw [hW, map_zero]
  rfl

/-- Every coefficient of `W` is in the finite span of designated closed tails. -/
theorem W_mem_finiteTailSpan (N r ell j : ℕ) (hell : ell < N * r) :
    W N r ell j ∈ finiteTailSpan N r ell := by
  unfold W
  split_ifs with hj
  · exact Submodule.neg_mem _ (tail_mem_finiteTailSpan N r ell j hell hj)
  · exact Submodule.zero_mem _

/-- The polynomial `P` has coefficients that are actual linear combinations
of the designated tails; no boundary corrections are introduced. -/
theorem P_mem_finiteTailSpan (N r ell j : ℕ) (hN : 0 < N) (hell : ell < N * r) :
    P N r ell j ∈ finiteTailSpan N r ell := by
  rw [P_eq_eulerOperator_W _ _ _ hN]
  exact eulerOperator_mem N r _ _ (fun k => W_mem_finiteTailSpan N r ell k hell) j

/-- A finite polynomial with the specified coefficients through degree `b`. -/
def finitePolynomial {B : Type*} [Semiring B] (b : ℕ) (Y : ℕ → B) : Polynomial B :=
  ∑ j ∈ Finset.range (b + 1), Polynomial.monomial j (Y j)

theorem coeff_finitePolynomial {B : Type*} [Semiring B] (b : ℕ) (Y : ℕ → B)
    (hY : ∀ j, b < j → Y j = 0) (j : ℕ) : (finitePolynomial b Y).coeff j = Y j := by
  classical
  simp only [finitePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hj
  · rfl
  · exact (hY j (by simpa using hj)).symm

theorem C_mem_degree_one (N r ell j : ℕ) :
    C N r ell j ∈ ExteriorAlgebra.exteriorPower (R r) 1 (CoefficientComplex.V r) := by
  unfold C
  split_ifs
  · exact Submodule.neg_mem _ (tail_mem_degree_one N r ell j)
  · exact Submodule.zero_mem _

theorem Q_mem_degree_one (N r ell j : ℕ) :
    Q N r ell j ∈ ExteriorAlgebra.exteriorPower (R r) 1 (CoefficientComplex.V r) := by
  apply Submodule.smul_mem
  exact eulerOperator_mem N r _ _ (tail_mem_degree_one N r ell) j

theorem P_mem_degree_one (N r ell j : ℕ) :
    P N r ell j ∈ ExteriorAlgebra.exteriorPower (R r) 1 (CoefficientComplex.V r) := by
  apply Submodule.sub_mem
  · exact Submodule.smul_mem _ _ (Q_mem_degree_one N r ell j)
  · exact eulerOperator_mem N r _ _ (C_mem_degree_one N r ell) j

/-- The actual polynomial `C`. -/
def cPolynomial (N r ell : ℕ) : Polynomial (A r) := finitePolynomial (N * r) (C N r ell)

@[simp] theorem coeff_cPolynomial (N r ell j : ℕ) : (cPolynomial N r ell).coeff j = C N r ell j := by
  apply coeff_finitePolynomial
  intro k hk
  exact if_neg (Nat.not_le.mpr hk)

/-- Polynomial Euler differentiation, also valid for the noncommutative chain algebra. -/
def polynomialEuler {B : Type*} [Semiring B] (Y : Polynomial B) : Polynomial B :=
  Polynomial.X * Y.derivative

@[simp] theorem coeff_polynomialEuler {B : Type*} [Semiring B] (Y : Polynomial B) (j : ℕ) :
    (polynomialEuler Y).coeff j = j • Y.coeff j := by
  cases j with
  | zero => simp [polynomialEuler]
  | succ j =>
    rw [polynomialEuler, Polynomial.coeff_X_mul, Polynomial.coeff_derivative,
      nsmul_eq_mul, Nat.cast_succ]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.cast_commute (j + 1) (Y.coeff (j + 1))).eq.symm

/-- The coefficient polynomial `E` included in the exterior chain algebra. -/
def scalarE (r : ℕ) : Polynomial (A r) :=
  (E r).map (algebraMap (R r) (A r))

theorem scalarE_eq (r : ℕ) : scalarE r = 1 +
    ∑ i : Fin r, Polynomial.monomial (i.val + 1) (algebraMap (R r) (A r) (e r i)) := by
  simp [scalarE, E, Polynomial.map_sum]

theorem polynomialEuler_scalarE (r : ℕ) : polynomialEuler (scalarE r) =
    ∑ i : Fin r, Polynomial.monomial (i.val + 1)
      (algebraMap (R r) (A r) (e r i * ((i.val + 1 : ℕ) : R r))) := by
  simp [polynomialEuler, scalarE_eq, map_sum, Finset.mul_sum, Polynomial.X_mul_monomial]

/-- The literal polynomial expression `S_E(Y) = E DY - N (DE)Y`. -/
def polynomialOperator (N r : ℕ) (Y : Polynomial (A r)) : Polynomial (A r) :=
  scalarE r * polynomialEuler Y - N • (polynomialEuler (scalarE r) * Y)

private theorem coeff_monomial_mul_guarded {B : Type*} [Semiring B]
    (Y : Polynomial B) (s j : ℕ) (c : B) :
    (Polynomial.monomial s c * Y).coeff j =
      if s ≤ j then c * Y.coeff (j - s) else 0 := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs <;> simp

private theorem coeff_sum_monomial_mul_guarded {B : Type*} [Semiring B]
    (r j : ℕ) (Y : Polynomial B) (c : Fin r → B) :
    ((∑ i : Fin r, Polynomial.monomial (i.val + 1) (c i)) * Y).coeff j =
      ∑ i : Fin r, if i.val + 1 ≤ j then c i * Y.coeff (j - (i.val + 1)) else 0 := by
  classical
  rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl (fun i _ => coeff_monomial_mul_guarded _ _ _ _)

/-- The finite coefficient formula is exactly the ordinary polynomial Euler expression. -/
theorem coeff_polynomialOperator (N r : ℕ) (Y : Polynomial (A r)) (j : ℕ) :
    (polynomialOperator N r Y).coeff j = eulerOperator N r Y.coeff j := by
  classical
  rw [polynomialOperator, Polynomial.coeff_sub, Polynomial.coeff_smul,
    polynomialEuler_scalarE, scalarE_eq, add_mul, one_mul, Polynomial.coeff_add,
    coeff_sum_monomial_mul_guarded,
    coeff_sum_monomial_mul_guarded]
  simp only [coeff_polynomialEuler, eulerOperator_apply, Nat.cast_smul_eq_nsmul,
    Finset.smul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · simp only [mul_smul_comm, ← Algebra.smul_def, ← Nat.cast_smul_eq_nsmul (R r),
      smul_smul, ← sub_smul]
    congr 1
    rw [Nat.cast_sub hi]
    push_cast
    ring
  · simp

theorem cPolynomial_natDegree_le (N r ell : ℕ) : (cPolynomial N r ell).natDegree ≤ N * r := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_cPolynomial, C, if_neg (Nat.not_le.mpr hj)]

end TailSeries
end TorusLinkHomology.CoefficientComplex
