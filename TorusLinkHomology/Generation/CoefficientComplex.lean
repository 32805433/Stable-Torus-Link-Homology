import DGA.Exterior
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Auxiliary coefficient Koszul complexes

The variable indexed by i : Fin r represents the coefficient e_{i+1}.
The initial odd generator with that index represents χ_{ell+i+1}.
The differential is exterior contraction, packaged by koszulDGA.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientComplex

abbrev R (r : ℕ) := MvPolynomial (Fin r) ℚ
abbrev V (r : ℕ) := Fin r →₀ R r
abbrev A (r : ℕ) := ExteriorAlgebra (R r) (V r)

/-- The coefficient e_{i+1}. -/
def e (r : ℕ) (i : Fin r) : R r := MvPolynomial.X i

/-- The auxiliary polynomial with constant coefficient one. -/
def E (r : ℕ) : Polynomial (R r) :=
  1 + ∑ i : Fin r, Polynomial.monomial (i.val + 1) (e r i)

/-- The coefficient G_j = [x^j] E(x)^N. -/
def G (N r j : ℕ) : R r := ((E r) ^ N).coeff j

@[simp] theorem E_coeff_zero (r : ℕ) : (E r).coeff 0 = 1 := by
  classical
  simp [E]

@[simp] theorem G_zero (N r : ℕ) : G N r 0 = 1 := by
  change Polynomial.constantCoeff (E r ^ N) = 1
  rw [map_pow]
  change (E r).coeff 0 ^ N = 1
  rw [E_coeff_zero, one_pow]

private def euler {S : Type*} [CommRing S] (p : Polynomial S) : Polynomial S :=
  Polynomial.X * p.derivative

private theorem euler_coeff {S : Type*} [CommRing S] (p : Polynomial S) (j : ℕ) :
    (euler p).coeff j = p.coeff j * (j : S) := by
  cases j with
  | zero => simp [euler]
  | succ j => simpa [euler, Polynomial.coeff_X_mul] using Polynomial.coeff_derivative p j

private theorem euler_power {S : Type*} [CommRing S] (p : Polynomial S) (N : ℕ) :
    p * euler (p ^ N) = Polynomial.C (N : S) * euler p * p ^ N := by
  cases N with
  | zero => simp [euler]
  | succ N =>
    simp only [euler]
    rw [Polynomial.derivative_pow_succ, pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

private theorem coeff_monomial_mul_of_le {S : Type*} [CommRing S]
    (p : Polynomial S) (s j : ℕ) (a : S) (h : s ≤ j) :
    (Polynomial.monomial s a * p).coeff j = a * p.coeff (j - s) := by
  simpa [Nat.sub_add_cancel h] using Polynomial.coeff_monomial_mul p s (j - s) a

private theorem euler_E (r : ℕ) :
    euler (E r) =
      ∑ i : Fin r, Polynomial.monomial (i.val + 1)
        (e r i * ((i.val + 1 : ℕ) : R r)) := by
  classical
  simp [euler, E, map_sum, Finset.mul_sum, Polynomial.X_mul_monomial, mul_comm]

private theorem coeff_sum_monomial_mul (r j : ℕ) (p : Polynomial (R r))
    (c : Fin r → R r) (hj : r ≤ j) :
    ((∑ i : Fin r, Polynomial.monomial (i.val + 1) (c i)) * p).coeff j =
      ∑ i : Fin r, c i * p.coeff (j - (i.val + 1)) := by
  classical
  rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  exact coeff_monomial_mul_of_le _ _ _ _ ((Nat.succ_le_of_lt i.isLt).trans hj)

private theorem coeff_E_mul (r j : ℕ) (p : Polynomial (R r)) (hj : r ≤ j) :
    (E r * p).coeff j =
      p.coeff j + ∑ i : Fin r, e r i * p.coeff (j - (i.val + 1)) := by
  rw [E, add_mul, one_mul, Polynomial.coeff_add, coeff_sum_monomial_mul _ _ _ _ hj]

/-- Euler's coefficient recurrence, in the range where no index is negative. -/
theorem coefficient_recurrence (N r j : ℕ) (hj : r ≤ j) :
    (j : R r) * G N r j =
      ∑ i : Fin r,
        (((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) *
          e r i * G N r (j - (i.val + 1)) := by
  classical
  have hs (i : Fin r) : i.val + 1 ≤ j := (Nat.succ_le_of_lt i.isLt).trans hj
  have h := congrArg (fun p : Polynomial (R r) => p.coeff j) (euler_power (E r) N)
  change (E r * euler (E r ^ N)).coeff j =
    (Polynomial.C (N : R r) * euler (E r) * E r ^ N).coeff j at h
  rw [coeff_E_mul _ _ _ hj, mul_assoc, Polynomial.coeff_C_mul, euler_E,
    coeff_sum_monomial_mul _ _ _ _ hj, Finset.mul_sum] at h
  simp only [euler_coeff, mul_assoc] at h
  have h' : G N r j * (j : R r) +
      ∑ i : Fin r, e r i * (G N r (j - (i.val + 1)) *
        ((j - (i.val + 1) : ℕ) : R r)) =
    ∑ i : Fin r, ((N : R r) * (e r i * ((i.val + 1 : ℕ) : R r))) *
      G N r (j - (i.val + 1)) := by
    simpa only [G, mul_assoc] using h
  have hsum :
      (∑ i : Fin r, ((N : R r) * (e r i * ((i.val + 1 : ℕ) : R r))) *
          G N r (j - (i.val + 1))) -
      (∑ i : Fin r, e r i * (G N r (j - (i.val + 1)) *
          ((j - (i.val + 1) : ℕ) : R r))) =
      ∑ i : Fin r,
        (((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) *
          e r i * G N r (j - (i.val + 1)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.cast_sub (hs i), Nat.cast_add, Nat.cast_one]
    ring
  calc
    (j : R r) * G N r j = G N r j * (j : R r) := mul_comm _ _
    _ = _ := eq_sub_of_add_eq h'
    _ = _ := hsum

private theorem coeff_monomial_mul_guarded {S : Type*} [CommRing S]
    (p : Polynomial S) (s j : ℕ) (a : S) :
    (Polynomial.monomial s a * p).coeff j =
      if s ≤ j then a * p.coeff (j - s) else 0 := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  split_ifs <;> simp

private theorem coeff_sum_monomial_mul_guarded (r j : ℕ) (p : Polynomial (R r))
    (c : Fin r → R r) :
    ((∑ i : Fin r, Polynomial.monomial (i.val + 1) (c i)) * p).coeff j =
      ∑ i : Fin r, if i.val + 1 ≤ j then c i * p.coeff (j - (i.val + 1)) else 0 := by
  classical
  rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl (fun i _ => coeff_monomial_mul_guarded _ _ _ _)

/-- Euler's coefficient recurrence for every coefficient index, with terms of
negative remaining index omitted rather than interpreted by natural subtraction. -/
theorem coefficient_recurrence_guarded (N r j : ℕ) :
    (j : R r) * G N r j =
      ∑ i : Fin r, if i.val + 1 ≤ j then
        (((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) *
          e r i * G N r (j - (i.val + 1)) else 0 := by
  classical
  have h := congrArg (fun p : Polynomial (R r) => p.coeff j) (euler_power (E r) N)
  change (E r * euler (E r ^ N)).coeff j =
    (Polynomial.C (N : R r) * euler (E r) * E r ^ N).coeff j at h
  conv_lhs at h => rw [E, add_mul, one_mul, Polynomial.coeff_add,
    coeff_sum_monomial_mul_guarded]
  rw [mul_assoc, Polynomial.coeff_C_mul, euler_E,
    coeff_sum_monomial_mul_guarded, Finset.mul_sum] at h
  simp only [euler_coeff, mul_ite, mul_zero] at h
  have h' : G N r j * (j : R r) +
      (∑ i : Fin r, if i.val + 1 ≤ j then e r i *
        (G N r (j - (i.val + 1)) * ((j - (i.val + 1) : ℕ) : R r)) else 0) =
      ∑ i : Fin r, if i.val + 1 ≤ j then
        ((N : R r) * (e r i * ((i.val + 1 : ℕ) : R r))) *
          G N r (j - (i.val + 1)) else 0 := by
    simpa only [G, E, mul_assoc] using h
  calc
    (j : R r) * G N r j = G N r j * (j : R r) := mul_comm _ _
    _ = _ := eq_sub_of_add_eq h'
    _ = _ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with hi
      · simp only [Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
        ring
      · simp

theorem E_natDegree_le (r : ℕ) : (E r).natDegree ≤ r := by
  classical
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.succ_le_of_lt i.isLt)

/-- Coefficients above the degree of E^N vanish. -/
theorem G_eq_zero (N r j : ℕ) (hj : N * r < j) : G N r j = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact (Polynomial.natDegree_pow_le_of_le N (E_natDegree_le r)).trans_lt hj

/-- The initial exterior generator χ_{ell+i+1}, with the offset implicit. -/
def xi (r : ℕ) (i : Fin r) : A r :=
  ExteriorAlgebra.ι (R r) (Finsupp.single i 1)

def differentialFunctional (N r ell : ℕ) : V r →ₗ[R r] R r :=
  Finsupp.linearCombination (R r) (fun i : Fin r => G N r (ell + i.val + 1))

/-- The coefficient Koszul DGA for the interval ell+1,...,ell+r. -/
def dga (N r ell : ℕ) : DGA (R r) (A r) :=
  ExteriorAlgebra.koszulDGA (R r) (V r) (differentialFunctional N r ell)

abbrev d (N r ell : ℕ) : A r →ₗ[R r] A r := (dga N r ell).d

@[simp] theorem d_xi (N r ell : ℕ) (i : Fin r) :
    d N r ell (xi r i) =
      algebraMap (R r) (A r) (G N r (ell + i.val + 1)) := by
  simp [d, dga, xi, differentialFunctional]

theorem d_squared (N r ell : ℕ) (a : A r) : d N r ell (d N r ell a) = 0 :=
  (dga N r ell).d_squared a

/-- An initial generator indexed by its coefficient index, zero outside the list. -/
def chi (r ell j : ℕ) : A r :=
  if h : ell < j ∧ j ≤ ell + r then
    xi r ⟨j - ell - 1, by omega⟩
  else 0

@[simp] theorem chi_eq_zero (r ell j : ℕ) (hj : j ≤ ell) : chi r ell j = 0 := by
  simp [chi, Nat.not_lt.mpr hj]

theorem d_chi (N r ell j : ℕ) (hj : ell < j) (hjr : j ≤ ell + r) :
    d N r ell (chi r ell j) = algebraMap (R r) (A r) (G N r j) := by
  rw [chi, dif_pos ⟨hj, hjr⟩, d_xi]
  congr 2
  change ell + (j - ell - 1) + 1 = j
  omega

@[simp] theorem chi_initial (r ell : ℕ) (i : Fin r) :
    chi r ell (ell + i.val + 1) = xi r i := by
  have hi := i.isLt
  rw [chi, dif_pos (by omega)]
  congr 1
  apply Fin.ext
  change ell + i.val + 1 - ell - 1 = i.val
  omega

/-- Reciprocal of a natural-number scalar, taken in the rational coefficient field. -/
def invNat (r j : ℕ) : R r := algebraMap ℚ (R r) (j : ℚ)⁻¹

theorem invNat_mul_nat (r j : ℕ) (hj : 0 < j) :
    invNat r j * (j : R r) = 1 := by
  change algebraMap ℚ (R r) (j : ℚ)⁻¹ * algebraMap ℚ (R r) (j : ℚ) = 1
  rw [← map_mul, inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hj)), map_one]

theorem nat_mul_invNat (r j : ℕ) (hj : 0 < j) :
    (j : R r) * invNat r j = 1 := by
  rw [mul_comm, invNat_mul_nat r j hj]

/-- The recursively extended generators; these are chains, not new algebra generators. -/
def tail (N r ell j : ℕ) : A r :=
  if _h : j ≤ ell + r then chi r ell j
  else
    invNat r j • ∑ i : Fin r,
      ((((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) * e r i) •
        tail N r ell (j - (i.val + 1))
termination_by j
decreasing_by omega

theorem tail_eq_chi (N r ell j : ℕ) (hj : j ≤ ell + r) :
    tail N r ell j = chi r ell j := by
  rw [tail, dif_pos hj]

@[simp] theorem tail_initial (N r ell : ℕ) (i : Fin r) :
    tail N r ell (ell + i.val + 1) = xi r i := by
  rw [tail_eq_chi _ _ _ _ (by have := i.isLt; omega), chi_initial]

@[simp] theorem tail_eq_zero (N r ell j : ℕ) (hj : j ≤ ell) :
    tail N r ell j = 0 := by
  rw [tail_eq_chi N r ell j (by omega), chi_eq_zero _ _ _ hj]

theorem tail_eq_of_gt (N r ell j : ℕ) (hj : ell + r < j) :
    tail N r ell j =
      invNat r j • ∑ i : Fin r,
        ((((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) * e r i) •
          tail N r ell (j - (i.val + 1)) := by
  rw [tail, dif_neg (Nat.not_le.mpr hj)]

/-- Every extended generator differentiates to the coefficient with the same index. -/
theorem d_tail (N r ell j : ℕ) (hj : ell < j) :
    d N r ell (tail N r ell j) = algebraMap (R r) (A r) (G N r j) := by
  classical
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases htop : j ≤ ell + r
    · rw [tail_eq_chi _ _ _ _ htop, d_chi _ _ _ _ hj htop]
    · have hgt : ell + r < j := Nat.lt_of_not_ge htop
      rw [tail_eq_of_gt _ _ _ _ hgt, map_smul, map_sum]
      have hdt (i : Fin r) :
          d N r ell (tail N r ell (j - (i.val + 1))) =
            algebraMap (R r) (A r) (G N r (j - (i.val + 1))) := by
        apply ih (j - (i.val + 1)) (by omega)
        have := i.isLt
        omega
      simp only [map_smul, hdt]
      have hrec :
          (∑ i : Fin r,
            ((((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) * e r i) •
              algebraMap (R r) (A r) (G N r (j - (i.val + 1)))) =
            (j : R r) • algebraMap (R r) (A r) (G N r j) := by
        have h := congrArg (algebraMap (R r) (A r))
          (coefficient_recurrence N r j (by omega))
        simpa only [map_sum, map_mul, Algebra.smul_def, mul_assoc] using h.symm
      rw [hrec, smul_smul, invNat_mul_nat _ _ (by omega), one_smul]

/-- Extended generators beyond the degree of E^N are cycles. -/
theorem tail_is_cycle (N r ell j : ℕ) (hell : ell < j) (hNr : N * r < j) :
    d N r ell (tail N r ell j) = 0 := by
  rw [d_tail _ _ _ _ hell, G_eq_zero _ _ _ hNr, map_zero]

/-- The denominator-free version of the tail recursion. -/
theorem tail_recurrence (N r ell j : ℕ) (hj : ell + r < j) :
    (j : R r) • tail N r ell j =
      ∑ i : Fin r,
        ((((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) * e r i) •
          tail N r ell (j - (i.val + 1)) := by
  rw [tail_eq_of_gt _ _ _ _ hj, smul_smul, nat_mul_invNat _ _ (by omega), one_smul]

theorem xi_mem_degree_one (r : ℕ) (i : Fin r) :
    xi r i ∈ ExteriorAlgebra.exteriorPower (R r) 1 (V r) := by
  change xi r i ∈ LinearMap.range (ExteriorAlgebra.ι (R r)) ^ 1
  rw [pow_one]
  exact ⟨Finsupp.single i 1, rfl⟩

theorem chi_mem_degree_one (r ell j : ℕ) :
    chi r ell j ∈ ExteriorAlgebra.exteriorPower (R r) 1 (V r) := by
  unfold chi
  split_ifs
  · exact xi_mem_degree_one _ _
  · exact Submodule.zero_mem _

/-- Every extended generator is an exterior-degree-one chain, including zero tails. -/
theorem tail_mem_degree_one (N r ell j : ℕ) :
    tail N r ell j ∈ ExteriorAlgebra.exteriorPower (R r) 1 (V r) := by
  classical
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj : j ≤ ell + r
    · rw [tail_eq_chi _ _ _ _ hj]
      exact chi_mem_degree_one _ _ _
    · rw [tail_eq_of_gt _ _ _ _ (Nat.lt_of_not_ge hj)]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem _ _ (ih _ (by omega))

/-- The span of the first r-1 designated tails. -/
def finiteTailSpan (N r ell : ℕ) : Submodule (R r) (A r) :=
  Submodule.span (R r)
    {a | ∃ j : ℕ, N * r < j ∧ j < (N + 1) * r ∧ a = tail N r ell j}

/-- All tails lie in the span of the first r-1 tails when ell is below the degree bound. -/
theorem tail_mem_finiteTailSpan (N r ell j : ℕ) (hell : ell < N * r)
    (hj : N * r < j) : tail N r ell j ∈ finiteTailSpan N r ell := by
  classical
  have hm : (N + 1) * r = N * r + r := by simp [Nat.add_mul]
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hupper : j < (N + 1) * r
    · exact Submodule.subset_span ⟨j, hj, hupper, rfl⟩
    · have hgt : ell + r < j := by omega
      rw [tail_eq_of_gt _ _ _ _ hgt]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro i _
      by_cases hi : N * r < j - (i.val + 1)
      · apply Submodule.smul_mem
        exact ih _ (by omega) hi
      · have hir : i.val + 1 = r := by
          have := i.isLt
          omega
        have hjr : j = (N + 1) * r := by
          have := i.isLt
          omega
        have hz :
            (((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) *
              e r i = 0 := by
          rw [hir, hjr, Nat.cast_mul, sub_self, zero_mul]
        rw [hz, zero_smul]
        exact Submodule.zero_mem _

/-- In the one-variable case the designated finite tail list is empty. -/
theorem tail_eq_zero_of_r_one (N ell j : ℕ) (hell : ell < N) (hj : N < j) :
    tail N 1 ell j = 0 := by
  have hspan : finiteTailSpan N 1 ell = ⊥ := by
    unfold finiteTailSpan
    have hs :
        {a : A 1 | ∃ k : ℕ, N * 1 < k ∧ k < (N + 1) * 1 ∧ a = tail N 1 ell k} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨k, hk, hk', _⟩
      omega
    rw [hs, Submodule.span_empty]
  have hmem := tail_mem_finiteTailSpan N 1 ell j (by simpa using hell) (by simpa using hj)
  simpa only [hspan, Submodule.mem_bot] using hmem

/-- In the finite-tail range the entire tail span consists of cycles. -/
theorem finiteTailSpan_le_ker (N r ell : ℕ) (hell : ell < N * r) :
    finiteTailSpan N r ell ≤ LinearMap.ker (d N r ell) := by
  apply Submodule.span_le.mpr
  rintro a ⟨j, hj, _, rfl⟩
  exact tail_is_cycle N r ell j (hell.trans hj) hj

end TorusLinkHomology.CoefficientComplex
