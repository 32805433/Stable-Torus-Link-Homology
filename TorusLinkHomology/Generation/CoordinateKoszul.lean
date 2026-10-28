import TorusLinkHomology.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Coefficient derivatives on a coordinate Koszul algebra

A basis extends a derivation of the coefficient ring to an additive connection
on a free module. Applied to the standard exterior basis, this differentiates
polynomial coefficients while keeping the exterior generators constant.

The coordinate-Koszul contraction is infrastructure for the offset-zero
auxiliary induction base, after its triangular polynomial coordinate change.
It is represented here by the original differential with exponent one; a
separate exponent-one branch in the final generation theorem is unnecessary.
-/

noncomputable section

namespace Module.Basis

variable {k R M I : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable [AddCommGroup M] [Module R M]

/-- Differentiate the coefficients in a chosen basis. -/
def coefficientConnection (b : Basis I R M) (δ : Derivation k R R) : M →+ M :=
  b.repr.symm.toAddEquiv.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom δ.toLinearMap.toAddMonoidHom).comp
      b.repr.toAddEquiv.toAddMonoidHom)

@[simp] theorem repr_coefficientConnection (b : Basis I R M)
    (δ : Derivation k R R) (x : M) (i : I) :
    b.repr (b.coefficientConnection δ x) i = δ (b.repr x i) := by
  simp [coefficientConnection]

/-- A coefficient connection kills each basis vector. -/
@[simp] theorem coefficientConnection_basis (b : Basis I R M)
    (δ : Derivation k R R) (i : I) :
    b.coefficientConnection δ (b i) = 0 := by
  classical
  apply b.repr.injective
  ext j
  simp only [repr_coefficientConnection, b.repr_self, map_zero, Finsupp.zero_apply]
  by_cases h : i = j <;> simp [h]

/-- The scalar Leibniz rule for the coefficient connection. -/
theorem coefficientConnection_smul (b : Basis I R M)
    (δ : Derivation k R R) (r : R) (x : M) :
    b.coefficientConnection δ (r • x) =
      δ r • x + r • b.coefficientConnection δ x := by
  apply b.repr.injective
  ext i
  simp [Derivation.leibniz, smul_eq_mul, mul_comm, add_comm]

/-- Coefficient differentiation of a single basis term. -/
@[simp] theorem coefficientConnection_smul_basis (b : Basis I R M)
    (δ : Derivation k R R) (r : R) (i : I) :
    b.coefficientConnection δ (r • b i) = δ r • b i := by
  rw [coefficientConnection_smul, coefficientConnection_basis, smul_zero, add_zero]

/-- Scalars from the ground ring are constant for the coefficient connection. -/
theorem coefficientConnection_ground_smul (b : Basis I R M)
    (δ : Derivation k R R) (r : k) (x : M) :
    b.coefficientConnection δ (algebraMap k R r • x) =
      algebraMap k R r • b.coefficientConnection δ x := by
  rw [coefficientConnection_smul, δ.map_algebraMap, zero_smul, zero_add]

/-- The commutator of a coefficient connection and a linear map is linear
over the coefficient ring. -/
def coefficientConnectionCommutator (b : Basis I R M) (δ : Derivation k R R)
    (f : M →ₗ[R] M) : M →ₗ[R] M where
  toFun x := b.coefficientConnection δ (f x) - f (b.coefficientConnection δ x)
  map_add' x y := by simp only [map_add]; abel
  map_smul' r x := by
    simp only [map_smul, coefficientConnection_smul, map_add, smul_sub]
    abel

@[simp] theorem coefficientConnectionCommutator_basis (b : Basis I R M)
    (δ : Derivation k R R) (f : M →ₗ[R] M) (i : I) :
    b.coefficientConnectionCommutator δ f (b i) =
      b.coefficientConnection δ (f (b i)) := by
  simp [coefficientConnectionCommutator]

/-- A connection commutator can be identified by checking basis vectors. -/
theorem coefficientConnection_commute_of_basis (b : Basis I R M)
    (δ : Derivation k R R) (f g : M →ₗ[R] M)
    (h : ∀ i, b.coefficientConnection δ (f (b i)) = g (b i)) (x : M) :
    b.coefficientConnection δ (f x) =
      f (b.coefficientConnection δ x) + g x := by
  have heq : b.coefficientConnectionCommutator δ f = g := by
    apply b.ext
    intro i
    simpa using h i
  have hx := DFunLike.congr_fun heq x
  change b.coefficientConnection δ (f x) - f (b.coefficientConnection δ x) = g x at hx
  rw [sub_eq_iff_eq_add] at hx
  exact hx.trans (add_comm _ _)

end Module.Basis

namespace TorusLinkHomology.CoordinateKoszul

theorem iota_eq_sum_xi (n : ℕ) (m : V n) :
    ExteriorAlgebra.ι (R n) m = ∑ j : Fin n, m j • xi n j := by
  have hm : (∑ j : Fin n, m j • Finsupp.single j (1 : R n)) = m :=
    (Finsupp.basisSingleOne : Module.Basis (Fin n) (R n) (V n)).sum_repr m
  calc
    ExteriorAlgebra.ι (R n) m =
        ExteriorAlgebra.ι (R n) (∑ j : Fin n, m j • Finsupp.single j (1 : R n)) :=
      congrArg (ExteriorAlgebra.ι (R n)) hm.symm
    _ = _ := by simp only [map_sum, map_smul, xi]

/-- Induction using polynomial scalars and the named exterior generators. -/
theorem induction_on_generators (n : ℕ) {P : A n → Prop}
    (hone : P 1) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (r : R n) a, P a → P (r • a))
    (hxi : ∀ j a, P a → P (xi n j * a)) (x : A n) : P x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simpa [Algebra.algebraMap_eq_smul_one] using hsmul r 1 hone
  | add a b ha hb => exact hadd a b ha hb
  | ι_mul a m ha =>
    change P (ExteriorAlgebra.ι (R n) m * a)
    rw [iota_eq_sum_xi, Finset.sum_mul]
    simp only [smul_mul_assoc]
    apply Finset.sum_induction _ _ hadd
    · simpa using hsmul 0 1 hone
    · intro j _
      exact hsmul (m j) (xi n j * a) (hxi j a ha)

/-- The standard basis of exterior monomials indexed by finite subsets. -/
def chainBasis (n : ℕ) : Module.Basis (Finset (Fin n)) (R n) (A n) :=
  (Finsupp.basisSingleOne : Module.Basis (Fin n) (R n) (V n)).ExteriorAlgebra

@[simp] theorem chainBasis_empty (n : ℕ) : chainBasis n ∅ = 1 := by
  rw [chainBasis, ExteriorAlgebra.basis_apply]
  exact ExteriorAlgebra.ιMulti_zero_apply _

@[simp] theorem chainBasis_singleton (n : ℕ) (j : Fin n) :
    chainBasis n {j} = xi n j := by
  rw [chainBasis, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton j)]
  simp [ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_singleton, xi]

/-- Partial differentiation of the polynomial coefficients of a chain. -/
def coefficientDerivative (n : ℕ) (i : Fin n) : A n →+ A n :=
  (chainBasis n).coefficientConnection (MvPolynomial.pderiv i)

@[simp] theorem repr_coefficientDerivative (n : ℕ) (i : Fin n) (x : A n)
    (s : Finset (Fin n)) :
    (chainBasis n).repr (coefficientDerivative n i x) s =
      MvPolynomial.pderiv i ((chainBasis n).repr x s) :=
  Module.Basis.repr_coefficientConnection _ _ _ _

@[simp] theorem coefficientDerivative_basis (n : ℕ) (i : Fin n)
    (s : Finset (Fin n)) :
    coefficientDerivative n i (chainBasis n s) = 0 :=
  Module.Basis.coefficientConnection_basis _ _ _

theorem coefficientDerivative_smul (n : ℕ) (i : Fin n) (r : R n) (x : A n) :
    coefficientDerivative n i (r • x) =
      MvPolynomial.pderiv i r • x + r • coefficientDerivative n i x :=
  Module.Basis.coefficientConnection_smul _ _ _ _

/-- In particular the coefficient derivative is linear over rational scalars. -/
theorem coefficientDerivative_rat_smul (n : ℕ) (i : Fin n) (r : ℚ) (x : A n) :
    coefficientDerivative n i ((MvPolynomial.C r : R n) • x) =
      (MvPolynomial.C r : R n) • coefficientDerivative n i x :=
  Module.Basis.coefficientConnection_ground_smul _ _ _ _

@[simp] theorem coefficientDerivative_one (n : ℕ) (i : Fin n) :
    coefficientDerivative n i 1 = 0 := by
  rw [← chainBasis_empty n, coefficientDerivative_basis]

@[simp] theorem coefficientDerivative_xi (n : ℕ) (i j : Fin n) :
    coefficientDerivative n i (xi n j) = 0 := by
  rw [← chainBasis_singleton n j, coefficientDerivative_basis]

/-- Products of standard exterior monomials have constant coefficients. -/
theorem coefficientDerivative_basis_mul (n : ℕ) (i : Fin n)
    (s t : Finset (Fin n)) :
    coefficientDerivative n i (chainBasis n s * chainBasis n t) = 0 := by
  let b : Module.Basis (Fin n) (R n) (V n) := Finsupp.basisSingleOne
  let S : Set.powersetCard (Fin n) s.card := Set.powersetCard.ofCard rfl
  let T : Set.powersetCard (Fin n) t.card := Set.powersetCard.ofCard rfl
  change coefficientDerivative n i (b.ExteriorAlgebra S * b.ExteriorAlgebra T) = 0
  by_cases h : Disjoint s t
  · rw [ExteriorAlgebra.basis_mul_of_disjoint b S T h]
    simp only [Units.smul_def, map_zsmul]
    change _ • coefficientDerivative n i (chainBasis n _) = 0
    rw [coefficientDerivative_basis, smul_zero]
  · rw [ExteriorAlgebra.basis_mul_of_not_disjoint b S T h, map_zero]

/-- Coefficient differentiation commutes with multiplication by a fixed
standard exterior monomial. -/
theorem coefficientDerivative_basis_mul_arbitrary (n : ℕ) (i : Fin n)
    (s : Finset (Fin n)) (x : A n) :
    coefficientDerivative n i (chainBasis n s * x) =
      chainBasis n s * coefficientDerivative n i x := by
  have h := (chainBasis n).coefficientConnection_commute_of_basis
    (MvPolynomial.pderiv i) (LinearMap.mulLeft (R n) (chainBasis n s)) 0
    (fun t => coefficientDerivative_basis_mul n i s t) x
  simpa [coefficientDerivative] using h

theorem coefficientDerivative_xi_mul (n : ℕ) (i j : Fin n) (x : A n) :
    coefficientDerivative n i (xi n j * x) = xi n j * coefficientDerivative n i x := by
  rw [← chainBasis_singleton n j, coefficientDerivative_basis_mul_arbitrary]

/-- The connection extends the usual partial derivative of polynomial scalars. -/
@[simp] theorem coefficientDerivative_algebraMap (n : ℕ) (i : Fin n) (r : R n) :
    coefficientDerivative n i (algebraMap (R n) (A n) r) =
      algebraMap (R n) (A n) (MvPolynomial.pderiv i r) := by
  rw [Algebra.algebraMap_eq_smul_one, coefficientDerivative_smul,
    coefficientDerivative_one, smul_zero, add_zero, Algebra.smul_def, mul_one]

/-- Differentiate the coordinates of a functional on the free generator module. -/
def functionalDerivative (n : ℕ) (i : Fin n) (f : Module.Dual (R n) (V n)) :
    Module.Dual (R n) (V n) :=
  Finsupp.linearCombination (R n)
    (fun j => MvPolynomial.pderiv i (f (Finsupp.single j 1)))

@[simp] theorem functionalDerivative_single (n : ℕ) (i j : Fin n)
    (f : Module.Dual (R n) (V n)) :
    functionalDerivative n i f (Finsupp.single j 1) =
      MvPolynomial.pderiv i (f (Finsupp.single j 1)) := by
  simp [functionalDerivative]

theorem contractLeft_xi_mul (n : ℕ) (f : Module.Dual (R n) (V n))
    (j : Fin n) (x : A n) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm (R n) (V n))) f (xi n j * x) =
      f (Finsupp.single j 1) • x -
        xi n j * CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm (R n) (V n))) f x :=
  CliffordAlgebra.contractLeft_ι_mul f _ _

/-- The commutator of a coefficient derivative with contraction is contraction
by the coordinatewise derivative of the functional. -/
theorem coefficientDerivative_contractLeft (n : ℕ) (i : Fin n)
    (f : Module.Dual (R n) (V n)) (x : A n) :
    coefficientDerivative n i
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm (R n) (V n))) f x) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm (R n) (V n))) f
          (coefficientDerivative n i x) +
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm (R n) (V n)))
          (functionalDerivative n i f) x := by
  induction x using induction_on_generators n with
  | hone => simp
  | hadd a b ha hb => simp only [map_add, ha, hb]; abel
  | hsmul r a ha =>
    simp only [map_smul, coefficientDerivative_smul, map_add, ha, smul_add]
    abel
  | hxi j a ha =>
    simp only [contractLeft_xi_mul, map_sub, coefficientDerivative_smul,
      coefficientDerivative_xi_mul, functionalDerivative_single, ha, mul_add]
    abel

/-- For exponent one, the coefficient equations are the independent variables. -/
@[simp] theorem differentialCoefficient_one (n : ℕ) (i : Fin n) :
    differentialCoefficient 1 n i = u n i := by
  classical
  simp only [differentialCoefficient, pow_one, uPolynomial,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact if_neg (fun h => hji (Fin.ext h))
  · simp

/-- Contraction by the coordinate dual to the named exterior generator. -/
def coordinateContraction (n : ℕ) (i : Fin n) : A n →ₗ[R n] A n :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm (R n) (V n)))
    (Finsupp.lapply i)

/-- The operator counting exterior degree. -/
def exteriorEuler (n : ℕ) : A n →ₗ[R n] A n :=
  ∑ i : Fin n, (LinearMap.mulLeft (R n) (xi n i)).comp (coordinateContraction n i)

@[simp] theorem exteriorEuler_apply (n : ℕ) (x : A n) :
    exteriorEuler n x = ∑ i : Fin n, xi n i * coordinateContraction n i x := by
  simp [exteriorEuler]

@[simp] theorem exteriorEuler_algebraMap (n : ℕ) (r : R n) :
    exteriorEuler n (algebraMap (R n) (A n) r) = 0 := by
  simp [exteriorEuler_apply, coordinateContraction]

theorem exteriorEuler_iota_mul (n : ℕ) (m : V n) (x : A n) :
    exteriorEuler n (ExteriorAlgebra.ι (R n) m * x) =
      ExteriorAlgebra.ι (R n) m * x + ExteriorAlgebra.ι (R n) m * exteriorEuler n x := by
  have hswap (i : Fin n) : xi n i * ExteriorAlgebra.ι (R n) m =
      -(ExteriorAlgebra.ι (R n) m * xi n i) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (Finsupp.single i 1) m)
  simp only [exteriorEuler_apply, coordinateContraction, CliffordAlgebra.contractLeft_ι_mul,
    Finsupp.lapply_apply, mul_sub, mul_smul_comm, ← mul_assoc, hswap,
    neg_mul, sub_neg_eq_add, Finset.sum_add_distrib]
  simp_rw [← smul_mul_assoc, mul_assoc]
  rw [← Finset.sum_mul, ← iota_eq_sum_xi, Finset.mul_sum]

/-- The exterior Euler operator acts by the exterior degree on each homogeneous piece. -/
theorem exteriorEuler_eq_nsmul {n p : ℕ} {x : A n} (hx : x ∈ koszulDegree n p) :
    exteriorEuler n x = p • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simpa only [zero_nsmul] using exteriorEuler_algebraMap n r
  | add x y p hx hy ihx ihy => simp only [map_add, ihx, ihy, nsmul_add]
  | mem_mul a ha p x hx ih =>
    obtain ⟨m, rfl⟩ := ha
    rw [exteriorEuler_iota_mul, ih]
    rw [show ExteriorAlgebra.ι (R n) m * (p • x) = p • (ExteriorAlgebra.ι (R n) m * x)
      from map_nsmul (LinearMap.mulLeft (R n) (ExteriorAlgebra.ι (R n) m)) p x]
    rw [succ_nsmul]
    exact add_comm _ _

@[simp] theorem functionalDerivative_coordinate (n : ℕ) (i : Fin n) :
    functionalDerivative n i (differentialFunctional 1 n) = Finsupp.lapply i := by
  apply (Finsupp.basisSingleOne : Module.Basis (Fin n) (R n) (V n)).ext
  intro j
  simp [Finsupp.coe_basisSingleOne, functionalDerivative,
    differentialFunctional, u, eq_comm]
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The partial derivative/contraction commutator for the coordinate Koszul differential. -/
theorem coefficientDerivative_d (n : ℕ) (i : Fin n) (x : A n) :
    coefficientDerivative n i (d 1 n x) =
      d 1 n (coefficientDerivative n i x) + coordinateContraction n i x := by
  simpa only [d, functionalDerivative_coordinate, coordinateContraction] using
    coefficientDerivative_contractLeft n i (differentialFunctional 1 n) x

/-- The polynomial/exterior Euler homotopy, before dividing by total degree. -/
def eulerHomotopy (n : ℕ) : A n →+ A n :=
  ∑ i : Fin n, (LinearMap.mulLeft (R n) (xi n i)).toAddMonoidHom.comp
    (coefficientDerivative n i)

@[simp] theorem eulerHomotopy_apply (n : ℕ) (x : A n) :
    eulerHomotopy n x = ∑ i : Fin n, xi n i * coefficientDerivative n i x := by
  simp [eulerHomotopy]

/-- The anticommutator with the coordinate Koszul differential is the sum
of the polynomial Euler operator and the exterior Euler operator. -/
theorem eulerHomotopy_identity (n : ℕ) (x : A n) :
    d 1 n (eulerHomotopy n x) + eulerHomotopy n (d 1 n x) =
      (∑ i : Fin n, u n i • coefficientDerivative n i x) +
        ∑ i : Fin n, xi n i * coordinateContraction n i x := by
  simp only [eulerHomotopy_apply, map_sum, d_xi_mul, differentialCoefficient_one,
    coefficientDerivative_d, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

/-- A closed chain on which the total Euler operator has positive eigenvalue
is a boundary, with an explicit divided Euler-homotopy witness. -/
theorem boundary_of_euler_eigenvalue (n : ℕ) {x : A n} {w : ℕ}
    (hw : 0 < w) (hx : d 1 n x = 0)
    (he : (∑ i : Fin n, u n i • coefficientDerivative n i x) +
      ∑ i : Fin n, xi n i * coordinateContraction n i x = w • x) :
    ∃ b : A n, d 1 n b = x := by
  have hd : d 1 n (eulerHomotopy n x) = w • x := by
    simpa only [hx, map_zero, add_zero] using (eulerHomotopy_identity n x).trans he
  have hw' : (w : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hw)
  refine ⟨(MvPolynomial.C ((w : ℚ)⁻¹) : R n) • eulerHomotopy n x, ?_⟩
  rw [map_smul, hd, ← Nat.cast_smul_eq_nsmul (R n), smul_smul]
  have hc : (MvPolynomial.C ((w : ℚ)⁻¹) : R n) * (w : R n) = 1 := by
    rw [← map_natCast (MvPolynomial.C : ℚ →+* R n) w,
      ← map_mul, inv_mul_cancel₀ hw', map_one]
  rw [hc, one_smul]

/-- Homogeneous closed chains of positive total degree are boundaries once
the polynomial Euler eigenvalue has been identified. -/
theorem boundary_of_bihomogeneous (n : ℕ) {x : A n} {a p : ℕ}
    (hw : 0 < a + p) (hx : d 1 n x = 0) (hp : x ∈ koszulDegree n p)
    (ha : ∑ i : Fin n, u n i • coefficientDerivative n i x = a • x) :
    ∃ b : A n, d 1 n b = x := by
  apply boundary_of_euler_eigenvalue n hw hx
  rw [ha, ← exteriorEuler_apply, exteriorEuler_eq_nsmul hp, add_nsmul]

end TorusLinkHomology.CoordinateKoszul
