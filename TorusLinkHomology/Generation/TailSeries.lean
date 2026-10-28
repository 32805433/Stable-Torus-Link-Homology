import TorusLinkHomology.Generation.ComparisonExplicit
import TorusLinkHomology.Generation.CoefficientSeries

/-!
# Actual tail-series identities

ET-01/02 are implemented coefficientwise. Multiplication by the polynomial
`E` involves only finitely many summands at each coefficient. The support
bounds below construct actual polynomials for `C`, `Q`, and `P`; the full
series `X` and `W` need not be polynomials.
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

/-- The Euler expression does not introduce lower powers of the series variable. -/
theorem eulerOperator_eq_zero_of_le (N r b : ℕ) [Module (R r) M] (Y : ℕ → M)
    (hY : ∀ j, j ≤ b → Y j = 0) (j : ℕ) (hj : j ≤ b) :
    eulerOperator N r Y j = 0 := by
  rw [eulerOperator_apply, hY j hj, smul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs
  · rw [hY _ ((Nat.sub_le _ _).trans hj), smul_zero]
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

/-- The lower coefficient polynomial `V=(E^N)_{≤ell}`, included in the chain algebra. -/
def V (N r ell : ℕ) (j : ℕ) : A r :=
  if j ≤ ell then algebraMap (R r) (A r) (G N r j) else 0

/-- Coefficients of `Q = -N⁻¹ S_E(X)`. -/
def Q (N r ell : ℕ) : ℕ → A r :=
  -(invNat r N) • eulerOperator N r (X N r ell)

/-- Coefficients of `P = NQ-S_E(C)`. -/
def P (N r ell : ℕ) : ℕ → A r :=
  (N : R r) • Q N r ell - eulerOperator N r (C N r ell)

theorem C_add_W (N r ell : ℕ) : C N r ell + W N r ell = -X N r ell := by
  funext j
  by_cases hj : j ≤ N * r <;> simp [C, W, hj, lt_iff_not_ge]

theorem d_X (N r ell j : ℕ) :
    d N r ell (X N r ell j) = algebraMap (R r) (A r) (G N r j) - V N r ell j := by
  by_cases hj : ell < j
  · simp only [X, d_tail N r ell j hj, V, if_neg (Nat.not_le.mpr hj), sub_zero]
  · rw [X, tail_eq_zero _ _ _ _ (Nat.le_of_not_gt hj), map_zero,
      V, if_pos (Nat.le_of_not_gt hj), sub_self]

theorem d_C (N r ell j : ℕ) (hell : ell ≤ N * r) :
    d N r ell (C N r ell j) = V N r ell j - algebraMap (R r) (A r) (G N r j) := by
  by_cases hj : j ≤ N * r
  · rw [C, if_pos hj, map_neg, d_X, neg_sub]
  · rw [C, if_neg hj, map_zero, V, if_neg (by omega),
      G_eq_zero _ _ _ (by omega), map_zero, sub_zero]

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

/-- Euler's recurrence is precisely `S_E(E^N)=0`. -/
theorem eulerOperator_G (N r j : ℕ) : eulerOperator N r (G N r) j = 0 := by
  rw [eulerOperator_apply]
  simp only [smul_eq_mul]
  rw [coefficient_recurrence_guarded]
  have hterm (i : Fin r) :
      (if i.val + 1 ≤ j then
        ((j : R r) - ((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r)) * e r i *
          G N r (j - (i.val + 1)) else 0) =
      -(if i.val + 1 ≤ j then
        (((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) * e r i *
          G N r (j - (i.val + 1)) else 0) := by
    split_ifs <;> ring
  simp only [hterm, Finset.sum_neg_distrib, add_neg_cancel]

theorem eulerOperator_scalar_G (N r j : ℕ) :
    eulerOperator N r (fun k => algebraMap (R r) (A r) (G N r k)) j = 0 := by
  simpa only [Algebra.linearMap_apply, eulerOperator_G, map_zero] using
    (map_eulerOperator N r (Algebra.linearMap (R r) (A r)) (G N r) j).symm

/-- The differential formula for `Q`, coefficient by coefficient. -/
theorem d_Q (N r ell j : ℕ) :
    d N r ell (Q N r ell j) = invNat r N • eulerOperator N r (V N r ell) j := by
  have hx : (fun k => d N r ell (X N r ell k)) =
      (fun k => algebraMap (R r) (A r) (G N r k)) - V N r ell := by
    funext k
    exact d_X N r ell k
  simp only [Q, Pi.smul_apply, neg_smul, map_neg, map_smul, map_eulerOperator, hx,
    map_sub, Pi.sub_apply, eulerOperator_scalar_G, zero_sub, smul_neg, neg_neg]

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

/-- `P` has finite support even though its expression `S_E(W)` uses an infinite tail. -/
theorem P_support (N r ell j : ℕ) (hell : ell ≤ N * r) (hj : N * r + r < j) :
    P N r ell j = 0 := by
  have hC : ∀ k, N * r < k → C N r ell k = 0 := by
    intro k hk
    exact if_neg (Nat.not_le.mpr hk)
  simp only [P, Pi.sub_apply, Pi.smul_apply,
    eulerOperator_support _ _ _ _ hC j hj, sub_zero]
  rw [Q_support N r ell j (by omega), smul_zero]

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

theorem Q_eq_zero_of_le (N r ell j : ℕ) (hj : j ≤ ell) : Q N r ell j = 0 := by
  have hX : ∀ k, k ≤ ell → X N r ell k = 0 := fun k hk => tail_eq_zero N r ell k hk
  change -(invNat r N) • eulerOperator N r (X N r ell) j = 0
  rw [eulerOperator_eq_zero_of_le _ _ _ _ hX j hj, smul_zero]

theorem P_eq_zero_of_le (N r ell j : ℕ) (hN : 0 < N) (hj : j ≤ N * r) :
    P N r ell j = 0 := by
  rw [P_eq_eulerOperator_W _ _ _ hN]
  apply eulerOperator_eq_zero_of_le N r (N * r) _ _ j hj
  intro k hk
  exact if_neg (Nat.not_lt.mpr hk)

/-- The actual polynomial `C`. -/
def cPolynomial (N r ell : ℕ) : Polynomial (A r) := finitePolynomial (N * r) (C N r ell)

/-- The actual polynomial `Q`, of degree at most `ell+r`. -/
def qPolynomial (N r ell : ℕ) : Polynomial (A r) := finitePolynomial (ell + r) (Q N r ell)

/-- The actual polynomial `P`, of degree at most `Nr+r` in the relevant offset range. -/
def pPolynomial (N r ell : ℕ) : Polynomial (A r) := finitePolynomial (N * r + r) (P N r ell)

@[simp] theorem coeff_cPolynomial (N r ell j : ℕ) : (cPolynomial N r ell).coeff j = C N r ell j := by
  apply coeff_finitePolynomial
  intro k hk
  exact if_neg (Nat.not_le.mpr hk)

@[simp] theorem coeff_qPolynomial (N r ell j : ℕ) : (qPolynomial N r ell).coeff j = Q N r ell j :=
  coeff_finitePolynomial _ _ (fun k hk => Q_support N r ell k hk) j

theorem coeff_pPolynomial (N r ell j : ℕ) (hell : ell ≤ N * r) :
    (pPolynomial N r ell).coeff j = P N r ell j :=
  coeff_finitePolynomial _ _ (fun k hk => P_support N r ell k hell hk) j

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

/-- The actual polynomial `P` satisfies its defining polynomial Euler identity. -/
theorem pPolynomial_eq (N r ell : ℕ) (hell : ell ≤ N * r) :
    pPolynomial N r ell = (N : R r) • qPolynomial N r ell -
      polynomialOperator N r (cPolynomial N r ell) := by
  ext j
  rw [coeff_pPolynomial _ _ _ _ hell, Polynomial.coeff_sub,
    Polynomial.coeff_smul, coeff_qPolynomial, coeff_polynomialOperator]
  have hC : (cPolynomial N r ell).coeff = C N r ell := funext (coeff_cPolynomial N r ell)
  rw [hC]
  rfl

theorem cPolynomial_natDegree_le (N r ell : ℕ) : (cPolynomial N r ell).natDegree ≤ N * r := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_cPolynomial, C, if_neg (Nat.not_le.mpr hj)]

theorem qPolynomial_natDegree_le (N r ell : ℕ) :
    (qPolynomial N r ell).natDegree ≤ ell + r := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_qPolynomial, Q_support _ _ _ _ hj]

theorem pPolynomial_natDegree_le (N r ell : ℕ) (hell : ell ≤ N * r) :
    (pPolynomial N r ell).natDegree ≤ N * r + r := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_pPolynomial _ _ _ _ hell, P_support _ _ _ _ hell hj]

/-- Every actual coefficient of the polynomial `P` is a closed designated-tail combination. -/
theorem pPolynomial_coeff_mem_finiteTailSpan (N r ell j : ℕ)
    (hN : 0 < N) (hell : ell < N * r) :
    (pPolynomial N r ell).coeff j ∈ finiteTailSpan N r ell := by
  rw [coeff_pPolynomial _ _ _ _ hell.le]
  exact P_mem_finiteTailSpan N r ell j hN hell

theorem d_pPolynomial_coeff (N r ell j : ℕ) (hN : 0 < N) (hell : ell ≤ N * r) :
    d N r ell ((pPolynomial N r ell).coeff j) = 0 := by
  rw [coeff_pPolynomial _ _ _ _ hell]
  exact d_P N r ell j hN hell

/-- Under comparison, the new tail series is the old one with its first
coefficient removed. The equality includes all coefficients below the offset. -/
theorem J_X (N r ell : ℕ) :
    (fun j => J N (r + 1) (ell + 1) (X N (r + 1) (ell + 1) j)) =
      X N (r + 1) ell - Pi.single (ell + 1) (xi (r + 1) 0) := by
  classical
  funext j
  by_cases hj : ell + 1 < j
  · simp only [X, J_tail _ _ _ _ hj, Nat.add_sub_cancel_right, Pi.sub_apply,
      Pi.single_eq_of_ne (by omega : j ≠ ell + 1), sub_zero]
  · rw [X, tail_eq_zero _ _ _ _ (by omega), map_zero, Pi.sub_apply]
    by_cases heq : j = ell + 1
    · subst j
      rw [Pi.single_eq_same]
      have h := tail_initial N (r + 1) ell (0 : Fin (r + 1))
      have h' : tail N (r + 1) ell (ell + 1) = xi (r + 1) 0 := by simpa using h
      rw [X, h', sub_self]
    · rw [Pi.single_eq_of_ne heq, X, tail_eq_zero _ _ _ _ (by omega), sub_zero]

/-- The omitted first coefficient accounts for the distinguished comparison term. -/
theorem eulerOperator_first_single (N r ell : ℕ) :
    eulerOperator N (r + 1) (Pi.single (ell + 1) (xi (r + 1) 0)) (ell + r + 2) =
      ((((ell + r + 2 : ℕ) : R (r + 1)) -
        ((N + 1 : ℕ) : R (r + 1)) * ((r + 1 : ℕ) : R (r + 1))) *
          e (r + 1) (Fin.last r)) • xi (r + 1) 0 := by
  classical
  rw [eulerOperator_apply, Pi.single_eq_of_ne (by omega : ell + r + 2 ≠ ell + 1),
    smul_zero, zero_add]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [if_pos (by simp; omega)]
    have heq : ell + r + 2 - ((Fin.last r).val + 1) = ell + 1 := by simp; omega
    rw [heq, Pi.single_eq_same]
    rfl
  · intro i _ hi
    split_ifs
    · have hind : ell + r + 2 - (i.val + 1) ≠ ell + 1 := by
        have hne : i.val ≠ r := by intro h; exact hi (Fin.ext h)
        have := i.isLt
        omega
      rw [Pi.single_eq_of_ne hind, smul_zero]
    · rfl
  · simp

/-- ET-02's final coefficient identity, before division by the deficit `m`. -/
theorem deficit_smul_etaPrime (N r ell : ℕ) (hm : ell + 1 < N * (r + 1)) :
    ((N * (r + 1) - (ell + 1) : ℕ) : R (r + 1)) • etaPrime N r ell =
      eulerOperator N (r + 1) (X N (r + 1) (ell + 1)) (ell + r + 2) := by
  apply J_injective N r ell hm
  rw [map_smul, J_etaPrime N r ell hm, smul_smul]
  change _ = (J N (r + 1) (ell + 1)).toLinearMap
    (eulerOperator N (r + 1) (X N (r + 1) (ell + 1)) (ell + r + 2))
  rw [map_eulerOperator]
  change _ = eulerOperator N (r + 1)
    (fun j => J N (r + 1) (ell + 1) (X N (r + 1) (ell + 1) j)) (ell + r + 2)
  rw [J_X, map_sub, Pi.sub_apply, eulerOperator_X_eq_zero _ _ _ _ (by omega),
    zero_sub, eulerOperator_first_single, ← neg_smul]
  congr 1
  rw [Nat.cast_sub (Nat.le_of_lt hm)]
  push_cast
  ring

/-- The distinguished generator is exactly `-N/m` times the top coefficient
of the actual polynomial `Q`; only the positive integer `m` is inverted. -/
theorem etaPrime_eq_qPolynomial_coeff (N r ell : ℕ)
    (hm : ell + 1 < N * (r + 1)) :
    etaPrime N r ell =
      (-((N : R (r + 1)) * invNat (r + 1) (N * (r + 1) - (ell + 1)))) •
        (qPolynomial N (r + 1) (ell + 1)).coeff (ell + r + 2) := by
  have hN : 0 < N := by
    by_contra h
    have hz : N = 0 := by omega
    simp only [hz, Nat.zero_mul] at hm
    omega
  have hmpos : 0 < N * (r + 1) - (ell + 1) := by omega
  have hQ := congrFun (nat_smul_Q N (r + 1) (ell + 1) hN) (ell + r + 2)
  change (N : R (r + 1)) • Q N (r + 1) (ell + 1) (ell + r + 2) =
    -eulerOperator N (r + 1) (X N (r + 1) (ell + 1)) (ell + r + 2) at hQ
  rw [← deficit_smul_etaPrime N r ell hm] at hQ
  have he := congrArg (fun z : A (r + 1) =>
    -(invNat (r + 1) (N * (r + 1) - (ell + 1))) • z) hQ
  simp only [smul_neg, smul_smul, neg_mul, invNat_mul_nat _ _ hmpos,
    neg_smul, one_smul, neg_neg] at he
  rw [coeff_qPolynomial]
  rw [mul_comm (N : R (r + 1)), neg_smul]
  exact he.symm

end TailSeries
end TorusLinkHomology.CoefficientComplex
