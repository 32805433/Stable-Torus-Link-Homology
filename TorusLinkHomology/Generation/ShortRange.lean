import TorusLinkHomology.Basic
import TorusLinkHomology.Generation.ExteriorCoordinates
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The two extremal minors of the explicit cycle matrix

The matrix has columns indexed by `j : Fin a`, corresponding to the cycle
`mu N (a + 1) (j + 1)`, and rows indexed by the odd generators. Its extremal
square submatrices are the two matrices needed for finite-adjugate descent.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.Generation

/-- The coefficient of `xi_i` in `mu_{j+1}`. -/
def muMatrix (N a : ℕ) : Matrix (Fin (a + 1)) (Fin a) (R (a + 1)) :=
  fun i j => if hij : i.val ≤ j.val + 1 then
    ((N : R (a + 1)) * ((j.val + 1 - i.val : ℕ) : R (a + 1)) -
      (i.val : R (a + 1))) *
      u (a + 1) ⟨j.val + 1 - i.val, by omega⟩
    else 0

/-- The square minor obtained by deleting row zero. -/
def muFirstMinor (N a : ℕ) : Matrix (Fin a) (Fin a) (R (a + 1)) :=
  (muMatrix N a).submatrix Fin.succ id

/-- The square minor obtained by deleting the last row. -/
def muLastMinor (N a : ℕ) : Matrix (Fin a) (Fin a) (R (a + 1)) :=
  (muMatrix N a).submatrix Fin.castSucc id

theorem muFirstMinor_upperTriangular (N a : ℕ) :
    (muFirstMinor N a).IsUpperTriangular := by
  intro i j hij
  change j.val < i.val at hij
  simp only [muFirstMinor, Matrix.submatrix_apply, id_eq, muMatrix, Fin.val_succ]
  rw [dif_neg (by exact Nat.not_le.mpr (Nat.succ_lt_succ hij))]

@[simp]
theorem muFirstMinor_diag (N a : ℕ) (i : Fin a) :
    muFirstMinor N a i i =
      -((i.val + 1 : ℕ) : R (a + 1)) * u (a + 1) 0 := by
  simp [muFirstMinor, muMatrix]

/-- The first maximal minor, in a form directly suitable for nonvanishing. -/
theorem muFirstMinor_det_prod (N a : ℕ) :
    (muFirstMinor N a).det =
      ∏ i : Fin a, (-((i.val + 1 : ℕ) : R (a + 1)) * u (a + 1) 0) := by
  rw [Matrix.det_of_isUpperTriangular (muFirstMinor_upperTriangular N a)]
  simp only [muFirstMinor_diag]

/-- The coefficient-ring endomorphism setting the constant variable to zero. -/
def killUZero (a : ℕ) : R (a + 1) →ₐ[ℚ] R (a + 1) :=
  MvPolynomial.aeval (fun i : Fin (a + 1) => if i.val = 0 then 0 else u (a + 1) i)

@[simp]
theorem killUZero_u (a : ℕ) (i : Fin (a + 1)) :
    killUZero a (u (a + 1) i) = if i.val = 0 then 0 else u (a + 1) i := by
  simp [killUZero, u]

/-- After setting `u₀ = 0`, the last maximal minor becomes upper triangular. -/
theorem muLastMinor_killUZero_upperTriangular (N a : ℕ) :
    ((muLastMinor N a).map (killUZero a)).IsUpperTriangular := by
  intro i j hij
  change j.val < i.val at hij
  simp only [Matrix.map_apply, muLastMinor, Matrix.submatrix_apply, id_eq,
    muMatrix, Fin.val_castSucc]
  split_ifs with h
  · have heq : j.val + 1 - i.val = 0 := by omega
    simp [heq]
  · exact map_zero _

@[simp]
theorem muLastMinor_killUZero_diag (N a : ℕ) (ha : 0 < a) (i : Fin a) :
    killUZero a (muLastMinor N a i i) =
      ((N : R (a + 1)) - (i.val : R (a + 1))) *
        u (a + 1) ⟨1, by omega⟩ := by
  simp [muLastMinor, muMatrix]

/-- The last maximal minor modulo the constant variable. -/
theorem muLastMinor_det_killUZero (N a : ℕ) (ha : 0 < a) :
    killUZero a (muLastMinor N a).det =
      ∏ i : Fin a, (((N : R (a + 1)) - (i.val : R (a + 1))) *
        u (a + 1) ⟨1, by omega⟩) := by
  rw [AlgHom.map_det]
  change ((muLastMinor N a).map (killUZero a)).det = _
  rw [Matrix.det_of_isUpperTriangular (muLastMinor_killUZero_upperTriangular N a)]
  apply Finset.prod_congr rfl
  intro i _
  exact muLastMinor_killUZero_diag N a ha i

/-- In the short range, the last minor remains nonzero modulo `u₀`. -/
theorem muLastMinor_det_killUZero_ne_zero (N a : ℕ) (haN : a ≤ N) :
    killUZero a (muLastMinor N a).det ≠ 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [muLastMinor]
  rw [muLastMinor_det_killUZero N a ha]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    exact fun h => (show N ≠ i.val by omega) (Nat.cast_inj.mp h)
  · exact MvPolynomial.X_ne_zero _

/-- The constant variable does not divide the last minor in the short range. -/
theorem uZero_not_dvd_muLastMinor_det (N a : ℕ) (haN : a ≤ N) :
    ¬u (a + 1) 0 ∣ (muLastMinor N a).det := by
  rintro ⟨b, hb⟩
  apply muLastMinor_det_killUZero_ne_zero N a haN
  rw [hb, map_mul, killUZero_u]
  simp

/-- The first minor is nonzero for every value of `N`. -/
theorem muFirstMinor_det_ne_zero (N a : ℕ) :
    (muFirstMinor N a).det ≠ 0 := by
  rw [muFirstMinor_det_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i.val)))
    (MvPolynomial.X_ne_zero _)

/-- The last minor is nonzero throughout the short range. -/
theorem muLastMinor_det_ne_zero (N a : ℕ) (haN : a ≤ N) :
    (muLastMinor N a).det ≠ 0 := by
  intro h
  exact muLastMinor_det_killUZero_ne_zero N a haN (by rw [h, map_zero])

/-- The coefficient matrix indeed gives the named one-cycles. -/
theorem mu_eq_sum_muMatrix (N a : ℕ) (j : Fin a) :
    mu N (a + 1) (j.val + 1) =
      ∑ i : Fin (a + 1), muMatrix N a i j • xi (a + 1) i := by
  unfold mu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  unfold muMatrix
  split_ifs with hij
  · let q : Fin (a + 1) := ⟨j.val + 1 - i.val, by omega⟩
    rw [Finset.sum_eq_single q]
    · simp only [q, show j.val + 1 - i.val + i.val = j.val + 1 by omega,
        ↓reduceIte]
    · intro b _ hb
      rw [if_neg]
      intro heq
      apply hb
      apply Fin.ext
      dsimp [q]
      omega
    · simp
  · rw [zero_smul]
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (by omega)]

/-- The two extremal minors are relatively prime throughout the short range.

This is relative primeness in a UFD, not the stronger assertion that the two
minors generate the unit ideal.
-/
theorem muExtremalMinors_isRelPrime (N a : ℕ) (haN : a ≤ N) :
    IsRelPrime (muFirstMinor N a).det (muLastMinor N a).det := by
  have hu : IsRelPrime (u (a + 1) 0) (muLastMinor N a).det :=
    ((MvPolynomial.X_prime (R := ℚ) (i := (0 : Fin (a + 1)))).irreducible.isRelPrime_iff_not_dvd).mpr
      (uZero_not_dvd_muLastMinor_det N a haN)
  rw [muFirstMinor_det_prod]
  apply IsRelPrime.prod_left
  intro i _
  apply IsRelPrime.mul_left _ hu
  apply IsUnit.isRelPrime_left
  have hq : IsUnit (-((i.val + 1 : ℕ) : ℚ)) :=
    isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)))
  simpa using hq.map (algebraMap ℚ (R (a + 1)))

/-- Closed form of the first maximal minor, including the empty minor. -/
theorem muFirstMinor_det (N a : ℕ) :
    (muFirstMinor N a).det =
      (-1 : R (a + 1)) ^ a * (a.factorial : R (a + 1)) * u (a + 1) 0 ^ a := by
  rw [muFirstMinor_det_prod, Finset.prod_mul_distrib, Finset.prod_neg]
  simp only [Finset.card_univ, Fintype.card_fin, Finset.prod_const]
  congr 1
  congr 1
  rw [← Nat.cast_prod]
  congr 1
  exact (Fin.prod_univ_eq_prod_range (fun i => i + 1) a).trans
    (Nat.factorial_eq_prod_range_add_one a).symm

/-- The full adapted matrix with the auxiliary basis vector in column zero,
followed by all the named cycles. -/
def muAdjoinedMatrix (N a : ℕ) (r : Fin (a + 1)) :
    Matrix (Fin (a + 1)) (Fin (a + 1)) (R (a + 1)) :=
  fun i j => Fin.cases (if i = r then 1 else 0) (muMatrix N a i) j

@[simp]
theorem muAdjoinedMatrix_zero (N a : ℕ) (r i : Fin (a + 1)) :
    muAdjoinedMatrix N a r i 0 = if i = r then 1 else 0 := by
  rfl

@[simp]
theorem muAdjoinedMatrix_succ (N a : ℕ) (r i : Fin (a + 1)) (j : Fin a) :
    muAdjoinedMatrix N a r i j.succ = muMatrix N a i j := by
  rfl

/-- Expanding along the auxiliary basis vector gives the signed maximal minor. -/
theorem muAdjoinedMatrix_det (N a : ℕ) (r : Fin (a + 1)) :
    (muAdjoinedMatrix N a r).det = (-1 : R (a + 1)) ^ r.val *
      ((muMatrix N a).submatrix r.succAbove id).det := by
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single r]
  · simp [muAdjoinedMatrix, Matrix.submatrix]
  · intro b _ hb
    simp [hb]
  · simp

@[simp]
theorem muAdjoinedMatrix_zero_det (N a : ℕ) :
    (muAdjoinedMatrix N a 0).det = (muFirstMinor N a).det := by
  simp [muAdjoinedMatrix_det, muFirstMinor]

@[simp]
theorem muAdjoinedMatrix_last_det (N a : ℕ) :
    (muAdjoinedMatrix N a (Fin.last a)).det =
      (-1 : R (a + 1)) ^ a * (muLastMinor N a).det := by
  simp [muAdjoinedMatrix_det, muLastMinor]

/-- The two full adapted matrices satisfy precisely the hypothesis of
`isInteger_exteriorAlgebra_coordinate_of_isRelPrime_dets`. -/
theorem muAdjoinedMatrices_isRelPrime (N a : ℕ) (haN : a ≤ N) :
    IsRelPrime (muAdjoinedMatrix N a 0).det
      (muAdjoinedMatrix N a (Fin.last a)).det := by
  rw [muAdjoinedMatrix_zero_det, muAdjoinedMatrix_last_det]
  exact (isUnit_neg_one.pow a).isRelPrime_right.mul_right
    (muExtremalMinors_isRelPrime N a haN)

end TorusLinkHomology.Generation
