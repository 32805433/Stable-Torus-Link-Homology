import TorusLinkHomology.Generation.CoordinateKoszul
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# A contraction of the coordinate Koszul complex

The total Euler operator is diagonal on the rational monomial/exterior basis.
Its inverse on positive total degrees gives a contraction onto the scalar copy
of `ℚ`. This is the coordinate-Koszul base case used by the generation proof.
-/

noncomputable section

namespace Module.Basis

variable {I M : Type*} [AddCommGroup M] [Module ℚ M]

/-- The diagonal linear operator with specified eigenvalues on a basis. -/
def rationalDiagonal (b : Basis I ℚ M) (w : I → ℚ) : M →ₗ[ℚ] M :=
  b.constr ℚ (fun i => w i • b i)

@[simp] theorem rationalDiagonal_basis (b : Basis I ℚ M) (w : I → ℚ) (i : I) :
    b.rationalDiagonal w (b i) = w i • b i := by
  exact b.constr_basis ℚ _ i

@[simp] theorem repr_rationalDiagonal (b : Basis I ℚ M) (w : I → ℚ) (x : M) (j : I) :
    b.repr (b.rationalDiagonal w x) j = w j * b.repr x j := by
  classical
  have he : (b.coord j).comp (b.rationalDiagonal w) = w j • b.coord j := by
    apply b.ext
    intro i
    by_cases h : i = j
    · simp [h]
    · simp [Ne.symm h]
  exact LinearMap.congr_fun he x

/-- Reciprocating the eigenvalues reciprocates the scalar on every eigenvector,
including the zero eigenspace, where the reciprocal is zero. -/
theorem rationalDiagonal_inv_of_eigenvector (b : Basis I ℚ M) (w : I → ℚ)
    {x : M} {c : ℚ} (hx : b.rationalDiagonal w x = c • x) :
    b.rationalDiagonal (fun i => (w i)⁻¹) x = c⁻¹ • x := by
  apply b.repr.injective
  ext i
  have hi := congrArg (fun y => b.repr y i) hx
  simp only [repr_rationalDiagonal, map_smul, Finsupp.smul_apply, smul_eq_mul] at hi ⊢
  by_cases hz : b.repr x i = 0
  · simp [hz]
  · rw [mul_right_cancel₀ hz hi]

end Module.Basis

namespace TorusLinkHomology.CoordinateKoszul

open scoped BigOperators

/-- Rational basis of polynomial monomials times exterior monomials. -/
def rationalChainBasis (n : ℕ) :
    Module.Basis ((Fin n →₀ ℕ) × Finset (Fin n)) ℚ (A n) :=
  (MvPolynomial.basisMonomials (Fin n) ℚ).smulTower (chainBasis n)

@[simp] theorem rationalChainBasis_apply (n : ℕ)
    (s : (Fin n →₀ ℕ) × Finset (Fin n)) :
    rationalChainBasis n s = MvPolynomial.monomial s.1 (1 : ℚ) • chainBasis n s.2 := by
  simp [rationalChainBasis, MvPolynomial.coe_basisMonomials]

/-- Total polynomial plus exterior degree of a rational basis vector. -/
def basisTotalDegree {n : ℕ} (s : (Fin n →₀ ℕ) × Finset (Fin n)) : ℕ :=
  (∑ i : Fin n, s.1 i) + s.2.card

theorem chainBasis_mem_degree (n : ℕ) (s : Finset (Fin n)) :
    chainBasis n s ∈ koszulDegree n s.card := by
  have he := ExteriorAlgebra.basis_eq_coe_basis
    (Finsupp.basisSingleOne : Module.Basis (Fin n) (R n) (V n))
    (Set.powersetCard.ofCard (s := s) rfl)
  simpa only [chainBasis] using he ▸
    ((Finsupp.basisSingleOne : Module.Basis (Fin n) (R n) (V n)).exteriorPower s.card
      (Set.powersetCard.ofCard rfl)).property

/-- The Euler anticommutator as a rational linear operator. -/
def totalEuler (n : ℕ) : A n →ₗ[ℚ] A n :=
  ((d 1 n).restrictScalars ℚ).comp (eulerHomotopy n).toRatLinearMap +
    (eulerHomotopy n).toRatLinearMap.comp ((d 1 n).restrictScalars ℚ)

@[simp] theorem totalEuler_apply (n : ℕ) (x : A n) :
    totalEuler n x = d 1 n (eulerHomotopy n x) + eulerHomotopy n (d 1 n x) := rfl

theorem totalEuler_eq_euler_sum (n : ℕ) (x : A n) :
    totalEuler n x = (∑ i : Fin n, u n i • coefficientDerivative n i x) +
      exteriorEuler n x := by
  simpa only [totalEuler_apply, exteriorEuler_apply] using eulerHomotopy_identity n x

theorem polynomialEuler_monomial_basis (n : ℕ) (m : Fin n →₀ ℕ) (s : Finset (Fin n)) :
    (∑ i : Fin n, u n i • coefficientDerivative n i
      (MvPolynomial.monomial m (1 : ℚ) • chainBasis n s)) =
      (∑ i : Fin n, m i) • (MvPolynomial.monomial m (1 : ℚ) • chainBasis n s) := by
  simp only [coefficientDerivative_smul, coefficientDerivative_basis, smul_zero, add_zero,
    smul_smul, u, MvPolynomial.X_mul_pderiv_monomial, smul_assoc]
  simp only [← Finset.sum_smul]

theorem totalEuler_basis (n : ℕ) (s : (Fin n →₀ ℕ) × Finset (Fin n)) :
    totalEuler n (rationalChainBasis n s) =
      (basisTotalDegree s : ℚ) • rationalChainBasis n s := by
  rw [totalEuler_eq_euler_sum, rationalChainBasis_apply,
    polynomialEuler_monomial_basis, map_smul,
    exteriorEuler_eq_nsmul (chainBasis_mem_degree n s.2)]
  rw [smul_comm (MvPolynomial.monomial s.1 (1 : ℚ)) s.2.card,
    ← add_nsmul, Nat.cast_smul_eq_nsmul]
  rfl

/-- The Euler operator preserves the differential. -/
theorem totalEuler_d (n : ℕ) (x : A n) :
    totalEuler n (d 1 n x) = d 1 n (totalEuler n x) := by
  simp only [totalEuler_apply, d_squared, map_zero, add_zero, map_add, zero_add]

/-- The Euler operator counts total degree on the rational basis. -/
theorem totalEuler_eq_diagonal (n : ℕ) :
    totalEuler n = (rationalChainBasis n).rationalDiagonal
      (fun s => (basisTotalDegree s : ℚ)) := by
  apply (rationalChainBasis n).ext
  intro s
  simpa only [Module.Basis.rationalDiagonal_basis] using totalEuler_basis n s

/-- The total-degree zero basis vector is the scalar unit. -/
theorem basisTotalDegree_eq_zero_iff (n : ℕ)
    (s : (Fin n →₀ ℕ) × Finset (Fin n)) :
    basisTotalDegree s = 0 ↔ s = (0, ∅) := by
  simp only [basisTotalDegree, Nat.add_eq_zero_iff, Finset.card_eq_zero]
  constructor
  · rintro ⟨hm, hs⟩
    apply Prod.ext
    · ext i
      exact (Finset.sum_eq_zero_iff.mp hm) i (Finset.mem_univ i)
    · exact hs
  · rintro rfl
    simp

@[simp] theorem rationalChainBasis_zero (n : ℕ) :
    rationalChainBasis n (0, ∅) = 1 := by
  simp [rationalChainBasis_apply]

/-- Divide by total degree, with value zero on degree zero. Every chain is a
finite sum in the rational basis, so this operator needs no infinite sums. -/
def inverseEuler (n : ℕ) : A n →ₗ[ℚ] A n :=
  (rationalChainBasis n).rationalDiagonal (fun s => (basisTotalDegree s : ℚ)⁻¹)

@[simp] theorem inverseEuler_basis (n : ℕ)
    (s : (Fin n →₀ ℕ) × Finset (Fin n)) :
    inverseEuler n (rationalChainBasis n s) =
      (basisTotalDegree s : ℚ)⁻¹ • rationalChainBasis n s := by
  exact Module.Basis.rationalDiagonal_basis _ _ _

/-- A total-degree eigenvector is divided by its eigenvalue. -/
theorem inverseEuler_of_eigenvector (n : ℕ) {x : A n} {c : ℚ}
    (hx : totalEuler n x = c • x) : inverseEuler n x = c⁻¹ • x := by
  exact (rationalChainBasis n).rationalDiagonal_inv_of_eigenvector
    (fun s => (basisTotalDegree s : ℚ)) (by rwa [← totalEuler_eq_diagonal])

/-- Division by total degree commutes with the differential. -/
theorem inverseEuler_d (n : ℕ) (x : A n) :
    inverseEuler n (d 1 n x) = d 1 n (inverseEuler n x) := by
  have he : (inverseEuler n).comp ((d 1 n).restrictScalars ℚ) =
      ((d 1 n).restrictScalars ℚ).comp (inverseEuler n) := by
    apply (rationalChainBasis n).ext
    intro s
    change inverseEuler n (d 1 n (rationalChainBasis n s)) =
      d 1 n (inverseEuler n (rationalChainBasis n s))
    rw [inverseEuler_basis, map_rat_smul]
    apply inverseEuler_of_eigenvector
    rw [totalEuler_d, totalEuler_basis, map_rat_smul]
  exact LinearMap.congr_fun he x

/-- Projection onto the scalar coefficient of exterior and polynomial degree zero. -/
def scalarProjection (n : ℕ) : A n →ₗ[ℚ] A n :=
  ((rationalChainBasis n).coord (0, ∅)).smulRight (1 : A n)

@[simp] theorem scalarProjection_apply (n : ℕ) (x : A n) :
    scalarProjection n x = (rationalChainBasis n).repr x (0, ∅) • (1 : A n) := rfl

@[simp] theorem scalarProjection_basis (n : ℕ)
    (s : (Fin n →₀ ℕ) × Finset (Fin n)) :
    scalarProjection n (rationalChainBasis n s) = if s = (0, ∅) then 1 else 0 := by
  classical
  simp only [scalarProjection_apply, Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simp_all

/-- Inverting the Euler operator recovers a chain modulo its scalar part. -/
theorem totalEuler_inverseEuler (n : ℕ) (x : A n) :
    totalEuler n (inverseEuler n x) = x - scalarProjection n x := by
  have he : (totalEuler n).comp (inverseEuler n) =
      LinearMap.id - scalarProjection n := by
    apply (rationalChainBasis n).ext
    intro s
    change totalEuler n (inverseEuler n (rationalChainBasis n s)) =
      rationalChainBasis n s - scalarProjection n (rationalChainBasis n s)
    rw [inverseEuler_basis, map_smul, totalEuler_basis, scalarProjection_basis, smul_smul]
    by_cases hs : s = (0, ∅)
    · subst s
      simp only [basisTotalDegree, Finsupp.coe_zero, Pi.zero_apply, Finset.sum_const_zero,
        Finset.card_empty, Nat.cast_zero, inv_zero, zero_mul, zero_smul,
        rationalChainBasis_zero, ↓reduceIte, sub_self, Nat.zero_add]
    · have hw : (basisTotalDegree s : ℚ) ≠ 0 := by
        exact_mod_cast mt ((basisTotalDegree_eq_zero_iff n s).mp) hs
      rw [inv_mul_cancel₀ hw, one_smul, if_neg hs, sub_zero]
  exact LinearMap.congr_fun he x

/-- The normalized Euler homotopy contracts every positive total-degree summand. -/
def coordinateHomotopy (n : ℕ) : A n →ₗ[ℚ] A n :=
  (eulerHomotopy n).toRatLinearMap.comp (inverseEuler n)

@[simp] theorem coordinateHomotopy_apply (n : ℕ) (x : A n) :
    coordinateHomotopy n x = eulerHomotopy n (inverseEuler n x) := rfl

/-- A chain homotopy from the identity to projection onto the scalar copy of `ℚ`. -/
theorem coordinateHomotopy_identity (n : ℕ) (x : A n) :
    d 1 n (coordinateHomotopy n x) + coordinateHomotopy n (d 1 n x) =
      x - scalarProjection n x := by
  rw [coordinateHomotopy_apply, coordinateHomotopy_apply, inverseEuler_d,
    ← totalEuler_apply, totalEuler_inverseEuler]

/-- Every cycle of the coordinate Koszul differential is a scalar plus a boundary.
The statement includes the empty-coordinate case. -/
theorem cycle_eq_scalar_add_boundary (n : ℕ) (x : A n) (hx : d 1 n x = 0) :
    ∃ r : ℚ, ∃ b : A n, x = r • (1 : A n) + d 1 n b := by
  refine ⟨(rationalChainBasis n).repr x (0, ∅), coordinateHomotopy n x, ?_⟩
  have he := coordinateHomotopy_identity n x
  rw [hx, map_zero, add_zero, scalarProjection_apply] at he
  exact (eq_sub_iff_add_eq.mp he).symm.trans (add_comm _ _)

end TorusLinkHomology.CoordinateKoszul
