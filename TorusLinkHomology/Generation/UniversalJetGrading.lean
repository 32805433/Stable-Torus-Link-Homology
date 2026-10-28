import TorusLinkHomology.Generation.UniversalJets
import TorusLinkHomology.Generation.MuCoordinatesGrading
import TorusLinkHomology.Generation.JetNormalization

/-! # Homogeneous polynomial coordinates of the universal selector identity -/

noncomputable section

namespace TorusLinkHomology.UniversalJets

open scoped BigOperators
open Generation

/-- Ordered products of coefficient-constant odd vectors stay constant
for the polynomial Euler operator. -/
theorem polynomialEuler_ιMulti_of_eq_zero (n q : ℕ) (v : Fin q → V n)
    (hv : ∀ i, polynomialEuler n (ExteriorAlgebra.ι (R n) (v i)) = 0) :
    polynomialEuler n (ExteriorAlgebra.ιMulti (R n) q v) = 0 := by
  induction q with
  | zero => rw [ExteriorAlgebra.ιMulti_zero_apply, polynomialEuler_one]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, polynomialEuler_mul, hv 0,
      ih (Matrix.vecTail v) (fun i => hv i.succ), zero_mul, mul_zero, add_zero]

theorem polynomialEuler_jetVector (N : ℕ) (p : Polynomial ℚ) (i : ℕ) :
    polynomialEuler (N + 1) (ExteriorAlgebra.ι (R (N + 1)) (jetVector N p i)) = 0 := by
  rw [jetVector, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_smul]
  change polynomialEuler (N + 1)
    (MvPolynomial.C (jetCoefficient p i j.val) • xi (N + 1) j) = 0
  rw [polynomialEuler_homogeneous_smul (N + 1) 0
    (MvPolynomial.isHomogeneous_C _ _), polynomialEuler_xi]
  simp

/-- Each summand has polynomial degree N: its one even factor has degree N,
and its q odd selector factors have coefficient degree zero. -/
theorem polynomialEuler_selectorCycle (N q : ℕ) (p : Polynomial ℚ) :
    polynomialEuler (N + 1) (selectorCycle N q p) = N • selectorCycle N q p := by
  unfold selectorCycle
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hcoefficient : (((-1 : R (N + 1)) ^ i.val) *
      jetDifferential N p i.val).IsHomogeneous N := by
    simpa using (jetDifferential_isHomogeneous N p i.val).C_mul ((-1 : ℚ) ^ i.val)
  rw [polynomialEuler_homogeneous_smul (N + 1) N hcoefficient]
  simp only [Function.comp_def]
  rw [polynomialEuler_ιMulti_of_eq_zero (N + 1) q _
    (fun j => polynomialEuler_jetVector N p (i.succAbove j).val), smul_zero, add_zero]

theorem selectorCycle_coefficients_homogeneous (N q : ℕ) (p : Polynomial ℚ)
    (s : Finset (Fin (N + 1))) :
    ((CoordinateKoszul.chainBasis (N + 1)).repr (selectorCycle N q p) s).IsHomogeneous N :=
  coefficients_homogeneous_of_polynomialEuler (N + 1) N
    (polynomialEuler_selectorCycle N q p) s

/-- The universal selector cycle has polynomial μ-coordinates of degree N−q,
with only q-fold exterior products. The separate jet degree bound identifies
this finite expression with the untruncated selector expression. -/
theorem exists_homogeneous_selector_coordinates (N q : ℕ) (p : Polynomial ℚ)
    (hq : q ≤ N) :
    ∃ w : PiCoordinates.PiA (N + 1),
      ExteriorAlgebra.map (muAdjoinedMatrix N N 0).toLin' w =
        PiCoordinates.toPi (N + 1) (selectorCycle N q p) ∧
      ExteriorAlgebra.map (eraseCoordinate 0) w = w ∧
      (∀ s, ((Pi.basisFun (R (N + 1)) (Fin (N + 1))).ExteriorAlgebra.repr w s).IsHomogeneous
        (N - q)) ∧
      (∀ s, s.card ≠ q →
        (Pi.basisFun (R (N + 1)) (Fin (N + 1))).ExteriorAlgebra.repr w s = 0) := by
  exact exists_homogeneous_mu_cycle_coordinates N N N q le_rfl hq _
    (selectorCycle_is_cycle N q p) (selectorCycle_coefficients_homogeneous N q p)
    (selectorCycle_mem_degree N q p)

end TorusLinkHomology.UniversalJets
