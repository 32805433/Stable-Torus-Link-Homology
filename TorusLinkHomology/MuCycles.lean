import TorusLinkHomology.Basic
import Mathlib.Algebra.Polynomial.Derivative

/-!
# The explicit generators are cycles

The polynomial identity `N (z u') u^N = u (z (u^N)')` gives the
coefficient syzygies defining the elements `mu`. Truncation does not change
the coefficients in degrees less than `n`.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology

private def finitePolynomial {S : Type*} [CommRing S] {n : ℕ}
    (c : Fin n → S) : Polynomial S :=
  ∑ i : Fin n, Polynomial.monomial i.val (c i)

private def euler {S : Type*} [CommRing S] (p : Polynomial S) : Polynomial S :=
  Polynomial.X * p.derivative

private theorem finitePolynomial_coeff {S : Type*} [CommRing S] {n k : ℕ}
    (c : Fin n → S) (hk : k < n) :
    (finitePolynomial c).coeff k = c ⟨k, hk⟩ := by
  classical
  simp only [finitePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro i _ hi
    exact if_neg (fun h => hi (Fin.ext h))
  · simp

private theorem euler_coeff {S : Type*} [CommRing S] (p : Polynomial S) (k : ℕ) :
    (euler p).coeff k = p.coeff k * (k : S) := by
  cases k with
  | zero => simp [euler]
  | succ k => simpa [euler, Polynomial.coeff_X_mul] using Polynomial.coeff_derivative p k

private theorem euler_finitePolynomial {S : Type*} [CommRing S] {n : ℕ}
    (c : Fin n → S) :
    euler (finitePolynomial c) = finitePolynomial (fun i => c i * (i.val : S)) := by
  classical
  unfold euler finitePolynomial
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : i.val with
  | zero => simp [hi]
  | succ j => simp [hi, Polynomial.X_mul_monomial]

private theorem weighted_coefficient {S : Type*} [CommRing S] {n : ℕ}
    (c b : Fin n → S) (N k : ℕ) :
    (∑ i : Fin n, ∑ j : Fin n,
      if i.val + j.val = k then
        (((N : S) * (i.val : S) - (j.val : S)) * c i) * b j else 0) =
    (Polynomial.C (N : S) * euler (finitePolynomial c) * finitePolynomial b -
      finitePolynomial c * euler (finitePolynomial b)).coeff k := by
  classical
  rw [euler_finitePolynomial, euler_finitePolynomial]
  simp only [finitePolynomial, Finset.mul_sum, Finset.sum_mul,
    Polynomial.C_mul_monomial, Polynomial.monomial_mul_monomial,
    Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    ← Finset.sum_sub_distrib]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

private theorem euler_power_identity {S : Type*} [CommRing S]
    (p : Polynomial S) (N : ℕ) :
    Polynomial.C (N : S) * euler p * p ^ N - p * euler (p ^ N) = 0 := by
  cases N with
  | zero => simp [euler]
  | succ N =>
    simp only [euler]
    rw [Polynomial.derivative_pow_succ, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

private theorem coeff_mul_congr_below {S : Type*} [CommRing S]
    (p q p' q' : Polynomial S) (k : ℕ)
    (hp : ∀ i ≤ k, p.coeff i = p'.coeff i)
    (hq : ∀ i ≤ k, q.coeff i = q'.coeff i) :
    (p * q).coeff k = (p' * q').coeff k := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have heq := Finset.mem_antidiagonal.mp hij
  rw [hp ij.1 (by omega), hq ij.2 (by omega)]

/-- The coefficient relation underlying the explicit cycles. -/
theorem mu_coefficient_relation (N n k : ℕ) (hk : k < n) :
    (∑ i : Fin n, ∑ j : Fin n,
      if i.val + j.val = k then
        (((N : R n) * (i.val : R n) - (j.val : R n)) * u n i) *
          differentialCoefficient N n j else 0) = 0 := by
  let p := uPolynomial n
  let q := finitePolynomial (differentialCoefficient N n)
  have hq (i : ℕ) (hi : i ≤ k) : q.coeff i = (p ^ N).coeff i := by
    exact finitePolynomial_coeff (differentialCoefficient N n) (lt_of_le_of_lt hi hk)
  rw [weighted_coefficient]
  change (Polynomial.C (N : R n) * euler p * q - p * euler q).coeff k = 0
  have hfirst : (Polynomial.C (N : R n) * euler p * q).coeff k =
      (Polynomial.C (N : R n) * euler p * p ^ N).coeff k :=
    coeff_mul_congr_below _ _ _ _ k (fun _ _ => rfl) hq
  have hsecond : (p * euler q).coeff k = (p * euler (p ^ N)).coeff k := by
    apply coeff_mul_congr_below _ _ _ _ k (fun _ _ => rfl)
    intro i hi
    rw [euler_coeff, euler_coeff, hq i hi]
  rw [Polynomial.coeff_sub, hfirst, hsecond, ← Polynomial.coeff_sub,
    euler_power_identity, Polynomial.coeff_zero]

/-- Every specified `mu_k` is a cycle. The assertion also holds for `k = 0`. -/
theorem mu_is_cycle (N n k : ℕ) (hk : k < n) : d N n (mu N n k) = 0 := by
  classical
  have h := congrArg (algebraMap (R n) (A n)) (mu_coefficient_relation N n k hk)
  simp only [mu, map_sum, apply_ite, map_zero, map_smul, d_xi]
  simpa only [map_sum, apply_ite, map_zero, Algebra.smul_def, map_mul] using h

end TorusLinkHomology
