import TorusLinkHomology.Generation.CoefficientSeries
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Polynomial selectors for exceptional coefficient indices

The roots are the unwanted Euler eigenvalues. The product formulas below
retain their signs and prove that the surviving scalar is nonzero even when
the exceptional range has fewer than `N` indices.
-/

noncomputable section

namespace TorusLinkHomology.CoefficientSelector

open scoped BigOperators
open Polynomial

/-- Remove the indices outside `T` among the first `k` deficits from `b`. -/
def selector (b : ℤ) (k : ℕ) (T : Finset ℕ) : Polynomial ℚ :=
  ∏ a ∈ Finset.range k \ T, (X - C ((b : ℚ) - (a : ℚ)))

theorem natDegree_selector (b : ℤ) (k : ℕ) (T : Finset ℕ) :
    (selector b k T).natDegree = (Finset.range k \ T).card := by
  classical
  rw [selector, Polynomial.natDegree_prod_of_monic (Finset.range k \ T)
    (f := fun a : ℕ => (X - C ((b : ℚ) - (a : ℚ)) : Polynomial ℚ))
    (fun a _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]

theorem natDegree_selector_of_subset (b : ℤ) (k : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range k) : (selector b k T).natDegree = k - T.card := by
  rw [natDegree_selector, Finset.card_sdiff_of_subset hT, Finset.card_range]

theorem eval_selector (b : ℤ) (k t : ℕ) (T : Finset ℕ) :
    (selector b k T).eval ((b : ℚ) - (t : ℚ)) =
      ∏ a ∈ Finset.range k \ T, ((a : ℚ) - (t : ℚ)) := by
  classical
  simp only [selector, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_congr rfl
  intro a _
  ring

theorem eval_selector_eq_zero (b : ℤ) (k t : ℕ) (T : Finset ℕ)
    (ht : t < k) (htT : t ∉ T) :
    (selector b k T).eval ((b : ℚ) - (t : ℚ)) = 0 := by
  rw [eval_selector]
  apply Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr ht, htT⟩)
  exact sub_self _

theorem eval_selector_ne_zero (b : ℤ) (k t : ℕ) (T : Finset ℕ) (ht : t ∈ T) :
    (selector b k T).eval ((b : ℚ) - (t : ℚ)) ≠ 0 := by
  rw [eval_selector]
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  apply sub_ne_zero.mpr
  intro hat
  have hat' : a = t := by exact_mod_cast hat
  exact (Finset.mem_sdiff.mp ha).2 (hat' ▸ ht)

/-- The unwanted exceptional coefficients are killed before any exterior products. -/
theorem coeff_evalEuler_selector_eq_zero {A : Type*} [Ring A] [Algebra ℚ A]
    (b : ℤ) (k t : ℕ) (T : Finset ℕ) (f : PowerSeries A)
    (ht : t < k) (htT : t ∉ T) :
    (CoefficientSeries.evalEuler (selector b k T) b f).coeff t = 0 := by
  apply CoefficientSeries.coeff_evalEuler_eq_zero
  simpa only [Int.cast_sub, Int.cast_natCast] using eval_selector_eq_zero b k t T ht htT

/-- The precise surviving coefficient, with its sign retained. -/
theorem coeff_evalEuler_selector {A : Type*} [Ring A] [Algebra ℚ A]
    (b : ℤ) (k t : ℕ) (T : Finset ℕ) (f : PowerSeries A) :
    (CoefficientSeries.evalEuler (selector b k T) b f).coeff t =
      (∏ a ∈ Finset.range k \ T, ((a : ℚ) - (t : ℚ))) • f.coeff t := by
  rw [CoefficientSeries.coeff_evalEuler]
  simp only [Int.cast_sub, Int.cast_natCast, eval_selector]

/-- The part of the transfer scalar that depends on the degree deficit `m`. -/
def fallingFactor (m k : ℕ) : ℚ :=
  ∏ a ∈ Finset.range k, ((m : ℚ) - (a : ℚ))

theorem fallingFactor_ne_zero (m k : ℕ) (hkm : k ≤ m) : fallingFactor m k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  have ham : a < m := lt_of_lt_of_le (Finset.mem_range.mp ha) hkm
  apply sub_ne_zero.mpr
  exact_mod_cast ham.ne'

/-- Vandermonde factor with the order of increasing selected deficits. -/
def pairFactor (T : Finset ℕ) : ℚ :=
  ∏ i ∈ T, ∏ j ∈ T.filter (i < ·), ((i : ℚ) - (j : ℚ))

theorem pairFactor_ne_zero (T : Finset ℕ) : pairFactor T ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  exact_mod_cast (Finset.mem_filter.mp hj).2.ne

/-- Factors contributed by evaluating the selector at the selected eigenvalues. -/
def crossFactor (k : ℕ) (T : Finset ℕ) : ℚ :=
  ∏ t ∈ T, ∏ a ∈ Finset.range k \ T, ((a : ℚ) - (t : ℚ))

theorem crossFactor_ne_zero (k : ℕ) (T : Finset ℕ) : crossFactor k T ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro t ht
  simpa only [eval_selector] using eval_selector_ne_zero 0 k t T ht

/-- The scalar in the exceptional-transfer coefficient identity. -/
def transferScalar (m k : ℕ) (T : Finset ℕ) : ℚ :=
  (-1) ^ (k - T.card) * pairFactor T * crossFactor k T * fallingFactor m k

theorem transferScalar_ne_zero (m k : ℕ) (T : Finset ℕ) (hkm : k ≤ m) :
    transferScalar m k T ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pairFactor_ne_zero T))
      (crossFactor_ne_zero k T)) (fallingFactor_ne_zero m k hkm)

/-- Scaling the columns of the transposed Vandermonde matrix by selector values. -/
theorem det_euler_matrix {n : ℕ} (p : Polynomial ℚ) (v : Fin n → ℚ) :
    Matrix.det (fun i j : Fin n => v j ^ i.val * p.eval (v j)) =
      (∏ j, p.eval (v j)) *
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
  have h := Matrix.det_mul_row (fun j => p.eval (v j)) (Matrix.vandermonde v).transpose
  have heq : Matrix.of (fun i j => p.eval (v j) * (Matrix.vandermonde v).transpose i j) =
      (fun i j : Fin n => v j ^ i.val * p.eval (v j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply, mul_comm]
  rw [heq] at h
  simpa only [Matrix.det_transpose, Matrix.det_vandermonde] using h

end TorusLinkHomology.CoefficientSelector
