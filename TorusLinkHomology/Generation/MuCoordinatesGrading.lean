import TorusLinkHomology.Generation.ShortRangeCycles
import TorusLinkHomology.Generation.CoordinateContraction
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Homogeneous degrees of integral named-cycle coordinates

This module supplies the grading control for UEI-017. Polynomial coefficient
degree and exterior degree are counted by separate Euler operators.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.Generation

open CoordinateKoszul

/-- The Euler operator counting polynomial coefficient degree only. -/
def polynomialEuler (n : ℕ) : A n →ₗ[ℚ] A n :=
  totalEuler n - (exteriorEuler n).restrictScalars ℚ

theorem polynomialEuler_apply (n : ℕ) (x : A n) :
    polynomialEuler n x = ∑ i : Fin n, u n i • coefficientDerivative n i x := by
  simp only [polynomialEuler, LinearMap.sub_apply, LinearMap.restrictScalars_apply,
    totalEuler_eq_euler_sum, add_sub_cancel_right]

@[simp] theorem polynomialEuler_basis (n : ℕ) (s : Finset (Fin n)) :
    polynomialEuler n (chainBasis n s) = 0 := by
  simp [polynomialEuler_apply]

@[simp] theorem polynomialEuler_one (n : ℕ) : polynomialEuler n 1 = 0 := by
  rw [← chainBasis_empty, polynomialEuler_basis]

@[simp] theorem polynomialEuler_xi (n : ℕ) (i : Fin n) :
    polynomialEuler n (xi n i) = 0 := by
  rw [← chainBasis_singleton, polynomialEuler_basis]

theorem polynomialEuler_smul (n : ℕ) (r : R n) (x : A n) :
    polynomialEuler n (r • x) =
      (∑ i : Fin n, u n i * MvPolynomial.pderiv i r) • x + r • polynomialEuler n x := by
  simp only [polynomialEuler_apply, coefficientDerivative_smul, smul_add,
    smul_smul, Finset.sum_add_distrib, Finset.sum_smul, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

theorem coefficientDerivative_mul (n : ℕ) (i : Fin n) (x y : A n) :
    coefficientDerivative n i (x * y) =
      coefficientDerivative n i x * y + x * coefficientDerivative n i y := by
  induction x using induction_on_generators n with
  | hone => simp
  | hadd x z hx hz => simp only [add_mul, map_add, hx, hz]; abel
  | hsmul r x hx =>
    simp only [smul_mul_assoc, coefficientDerivative_smul, hx, smul_add,
      add_mul]
    abel
  | hxi j x hx =>
    simp only [mul_assoc, coefficientDerivative_xi_mul, hx, mul_add]

theorem polynomialEuler_mul (n : ℕ) (x y : A n) :
    polynomialEuler n (x * y) = polynomialEuler n x * y + x * polynomialEuler n y := by
  simp only [polynomialEuler_apply, coefficientDerivative_mul, smul_add,
    smul_mul_assoc, mul_smul_comm, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

/-- Polynomial Euler eigenvectors have homogeneous polynomial coordinates. -/
theorem coefficients_homogeneous_of_polynomialEuler (n D : ℕ) {x : A n}
    (hx : polynomialEuler n x = D • x) :
    ∀ s, ((chainBasis n).repr x s).IsHomogeneous D := by
  have hb (s : (Fin n →₀ ℕ) × Finset (Fin n)) :
      polynomialEuler n (rationalChainBasis n s) =
        ((∑ i : Fin n, s.1 i : ℕ) : ℚ) • rationalChainBasis n s := by
    rw [polynomialEuler_apply, rationalChainBasis_apply, polynomialEuler_monomial_basis,
      Nat.cast_smul_eq_nsmul]
  have hdiag : polynomialEuler n = (rationalChainBasis n).rationalDiagonal
      (fun s => ((∑ i : Fin n, s.1 i : ℕ) : ℚ)) := by
    apply (rationalChainBasis n).ext
    intro s
    simpa only [Module.Basis.rationalDiagonal_basis] using hb s
  intro s m hm
  have he := congrArg (fun y => (rationalChainBasis n).repr y (m, s)) hx
  rw [hdiag, Module.Basis.repr_rationalDiagonal, map_nsmul, Finsupp.nsmul_apply,
    nsmul_eq_mul] at he
  have hc : (rationalChainBasis n).repr x (m, s) = MvPolynomial.coeff m ((chainBasis n).repr x s) :=
    (MvPolynomial.basisMonomials (Fin n) ℚ).smulTower_repr (chainBasis n) x (m, s)
  rw [hc] at he
  have hdeg : (∑ i : Fin n, m i) = D := by
    exact_mod_cast (mul_right_cancel₀ hm he)
  change (Finsupp.weight (fun _ : Fin n => (1 : ℕ))) m = D
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum]
  exact hdeg

/-- Conversely, homogeneous polynomial coordinates give the expected Euler eigenvalue. -/
theorem polynomialEuler_of_coefficients_homogeneous (n D : ℕ) {x : A n}
    (hx : ∀ s, ((chainBasis n).repr x s).IsHomogeneous D) :
    polynomialEuler n x = D • x := by
  apply (chainBasis n).repr.injective
  ext s : 1
  simp only [polynomialEuler_apply, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, repr_coefficientDerivative, smul_eq_mul,
    map_nsmul]
  exact (hx s).sum_X_mul_pderiv

theorem polynomialEuler_homogeneous_smul (n D : ℕ) {r : R n}
    (hr : r.IsHomogeneous D) (x : A n) :
    polynomialEuler n (r • x) = D • (r • x) + r • polynomialEuler n x := by
  rw [polynomialEuler_smul, show (∑ i : Fin n, u n i * MvPolynomial.pderiv i r) = D • r
    from hr.sum_X_mul_pderiv, smul_assoc]

/-- The entries of each named-cycle column have polynomial degree one. -/
theorem muMatrix_isHomogeneous (N a : ℕ) (i : Fin (a + 1)) (j : Fin a) :
    (muMatrix N a i j).IsHomogeneous 1 := by
  classical
  unfold muMatrix
  split_ifs with h
  · have hc : ((N : R (a + 1)) * ((j.val + 1 - i.val : ℕ) : R (a + 1)) -
        (i.val : R (a + 1))) = MvPolynomial.C
        ((N : ℚ) * (j.val + 1 - i.val : ℕ) - (i.val : ℚ)) := by simp
    rw [hc]
    exact (MvPolynomial.isHomogeneous_X ℚ _).C_mul _
  · apply MvPolynomial.isHomogeneous_zero

@[simp] theorem polynomialEuler_mu (N a : ℕ) (j : Fin a) :
    polynomialEuler (a + 1) (mu N (a + 1) (j.val + 1)) =
      mu N (a + 1) (j.val + 1) := by
  rw [mu_eq_sum_muMatrix, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [polynomialEuler_homogeneous_smul _ _ (muMatrix_isHomogeneous N a i j),
    polynomialEuler_xi, smul_zero, add_zero, one_nsmul]

/-- Exterior Euler commutes with any algebra map taking generators to degree one. -/
theorem exteriorEuler_algHom (n : ℕ) (f : A n →ₐ[R n] A n)
    (hf : ∀ i, f (xi n i) ∈ koszulDegree n 1) (x : A n) :
    exteriorEuler n (f x) = f (exteriorEuler n x) := by
  have hmul (i : Fin n) (y : A n) :
      exteriorEuler n (f (xi n i) * y) = f (xi n i) * y + f (xi n i) * exteriorEuler n y := by
    have hi := hf i
    change f (xi n i) ∈ LinearMap.range (ExteriorAlgebra.ι (R n)) ^ 1 at hi
    rw [pow_one] at hi
    obtain ⟨v, hv⟩ := hi
    rw [← hv, exteriorEuler_iota_mul]
  induction x using induction_on_generators n with
  | hone => simp [coordinateContraction]
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul r x hx => simp only [map_smul, hx]
  | hxi i x hx =>
    rw [map_mul, hmul, hx, show exteriorEuler n (xi n i * x) =
      xi n i * x + xi n i * exteriorEuler n x from exteriorEuler_iota_mul n _ x]
    simp only [map_add, map_mul]

/-- Substitution of polynomial-degree-one cycles adds exterior degree to
polynomial degree. Killing a generator is allowed. -/
theorem polynomialEuler_algHom (n : ℕ) (f : A n →ₐ[R n] A n)
    (hf : ∀ i, polynomialEuler n (f (xi n i)) = f (xi n i)) (x : A n) :
    polynomialEuler n (f x) = f (polynomialEuler n x) + f (exteriorEuler n x) := by
  induction x using induction_on_generators n with
  | hone => simp [coordinateContraction]
  | hadd x y hx hy => simp only [map_add, hx, hy]; abel
  | hsmul r x hx =>
    simp only [map_smul, polynomialEuler_smul, map_add, hx, smul_add]
    abel
  | hxi i x hx =>
    rw [map_mul, polynomialEuler_mul, hf, hx,
      show exteriorEuler n (xi n i * x) = xi n i * x + xi n i * exteriorEuler n x
        from exteriorEuler_iota_mul n _ x,
      polynomialEuler_mul, polynomialEuler_xi]
    simp only [zero_mul, zero_add, map_mul, map_add, mul_add]
    abel

/-- A substitution constant in the polynomial variables commutes with
coefficient Euler. -/
theorem polynomialEuler_algHom_constant (n : ℕ) (f : A n →ₐ[R n] A n)
    (hf : ∀ i, polynomialEuler n (f (xi n i)) = 0) (x : A n) :
    polynomialEuler n (f x) = f (polynomialEuler n x) := by
  induction x using induction_on_generators n with
  | hone => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul r x hx => simp only [map_smul, polynomialEuler_smul, hx, map_add]
  | hxi i x hx =>
    simp only [map_mul, polynomialEuler_mul, hf, hx, polynomialEuler_xi,
      zero_mul, zero_add]

/-- The first adapted matrix, transported back to the original exterior algebra. -/
def adaptedMuMap (N a : ℕ) : A (a + 1) →ₐ[R (a + 1)] A (a + 1) :=
  (PiCoordinates.toPi (a + 1)).symm.toAlgHom.comp
    ((ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin').comp
      (PiCoordinates.toPi (a + 1)).toAlgHom)

/-- Erase the auxiliary generator, in the original exterior coordinates. -/
def eraseAuxiliary (a : ℕ) : A (a + 1) →ₐ[R (a + 1)] A (a + 1) :=
  (PiCoordinates.toPi (a + 1)).symm.toAlgHom.comp
    ((ExteriorAlgebra.map (eraseCoordinate 0)).comp (PiCoordinates.toPi (a + 1)).toAlgHom)

@[simp] theorem adaptedMuMap_xi_zero (N a : ℕ) :
    adaptedMuMap N a (xi (a + 1) 0) = xi (a + 1) 0 := by
  have hc : (muAdjoinedMatrix N a 0).toLin'
      (Pi.basisFun (R (a + 1)) (Fin (a + 1)) 0) =
      Pi.basisFun (R (a + 1)) (Fin (a + 1)) 0 := by
    ext i
    simp [Matrix.toLin'_apply, muAdjoinedMatrix, Pi.basisFun_apply, Pi.single_apply]
  simp only [adaptedMuMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    PiCoordinates.toPi_xi, ExteriorAlgebra.map_apply_ι, hc]
  rw [← PiCoordinates.toPi_xi, AlgEquiv.symm_apply_apply]

@[simp] theorem adaptedMuMap_xi_succ (N a : ℕ) (j : Fin a) :
    adaptedMuMap N a (xi (a + 1) j.succ) = mu N (a + 1) (j.val + 1) := by
  have hc : (muAdjoinedMatrix N a 0).toLin'
      (Pi.basisFun (R (a + 1)) (Fin (a + 1)) j.succ) =
      (fun i => muMatrix N a i j) := by
    ext i
    simp [Matrix.toLin'_apply]
  simp only [adaptedMuMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    PiCoordinates.toPi_xi, ExteriorAlgebra.map_apply_ι, hc]
  rw [← PiCoordinates.toPi_mu, AlgEquiv.symm_apply_apply]

@[simp] theorem eraseAuxiliary_xi_zero (a : ℕ) :
    eraseAuxiliary a (xi (a + 1) 0) = 0 := by
  simp only [eraseAuxiliary, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    PiCoordinates.toPi_xi, ExteriorAlgebra.map_apply_ι, eraseCoordinate_basis,
    ↓reduceIte, map_zero]

@[simp] theorem eraseAuxiliary_xi_succ (a : ℕ) (j : Fin a) :
    eraseAuxiliary a (xi (a + 1) j.succ) = xi (a + 1) j.succ := by
  simp only [eraseAuxiliary, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    PiCoordinates.toPi_xi, ExteriorAlgebra.map_apply_ι, eraseCoordinate_basis,
    Fin.succ_ne_zero, ↓reduceIte]
  rw [← PiCoordinates.toPi_xi, AlgEquiv.symm_apply_apply]

theorem adaptedMuMap_injective (N a : ℕ) : Function.Injective (adaptedMuMap N a) :=
  (PiCoordinates.toPi (a + 1)).symm.injective.comp
    ((muAdjoinedMatrix_zero_map_injective N a).comp (PiCoordinates.toPi (a + 1)).injective)

@[simp] theorem polynomialEuler_eraseAuxiliary (a : ℕ) (x : A (a + 1)) :
    polynomialEuler (a + 1) (eraseAuxiliary a x) =
      eraseAuxiliary a (polynomialEuler (a + 1) x) := by
  apply polynomialEuler_algHom_constant
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [eraseAuxiliary_xi_zero,
    eraseAuxiliary_xi_succ, map_zero, polynomialEuler_xi]

theorem exteriorEuler_adaptedMuMap (N a : ℕ) (x : A (a + 1)) :
    exteriorEuler (a + 1) (adaptedMuMap N a x) =
      adaptedMuMap N a (exteriorEuler (a + 1) x) := by
  apply exteriorEuler_algHom
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [adaptedMuMap_xi_zero]
    change xi (a + 1) 0 ∈ LinearMap.range (ExteriorAlgebra.ι (R (a + 1))) ^ 1
    rw [pow_one]
    exact ⟨Finsupp.single 0 1, rfl⟩
  · rw [adaptedMuMap_xi_succ]
    exact mu_mem_degree_one _ _ _

/-- The substitution by named cycles has polynomial degree shift equal to exterior degree. -/
theorem polynomialEuler_muSubstitution (N a : ℕ) (x : A (a + 1)) :
    polynomialEuler (a + 1) (adaptedMuMap N a (eraseAuxiliary a x)) =
      adaptedMuMap N a (eraseAuxiliary a (polynomialEuler (a + 1) x)) +
        adaptedMuMap N a (eraseAuxiliary a (exteriorEuler (a + 1) x)) := by
  apply polynomialEuler_algHom (a + 1) ((adaptedMuMap N a).comp (eraseAuxiliary a))
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp only [AlgHom.comp_apply, eraseAuxiliary_xi_zero, eraseAuxiliary_xi_succ,
      map_zero, adaptedMuMap_xi_succ, polynomialEuler_mu]

/-- UEI-017: uniqueness forces the coefficient-degree shift on actual integral
coordinates. The auxiliary coordinate is absent, so all `q` odd factors map to
polynomial-degree-one named cycles. -/
theorem mu_coordinates_euler (N a D q : ℕ) (hqD : q ≤ D)
    {x v : A (a + 1)} (hv : adaptedMuMap N a v = x)
    (hp : eraseAuxiliary a v = v)
    (hx : polynomialEuler (a + 1) x = D • x)
    (hq : exteriorEuler (a + 1) x = q • x) :
    polynomialEuler (a + 1) v = (D - q) • v ∧
      exteriorEuler (a + 1) v = q • v := by
  have hqv : exteriorEuler (a + 1) v = q • v := by
    apply adaptedMuMap_injective N a
    rw [← exteriorEuler_adaptedMuMap, hv, hq, map_nsmul, hv]
  have hpe : eraseAuxiliary a (polynomialEuler (a + 1) v) =
      polynomialEuler (a + 1) v := by
    rw [← polynomialEuler_eraseAuxiliary, hp]
  have he := polynomialEuler_muSubstitution N a v
  rw [hp, hv, hx, hpe, hqv, map_nsmul, hp, map_nsmul, hv] at he
  have hc : adaptedMuMap N a (polynomialEuler (a + 1) v) = (D - q) • x := by
    apply add_right_cancel (b := q • x)
    rw [← he, ← add_nsmul, Nat.sub_add_cancel hqD]
  refine ⟨?_, hqv⟩
  apply adaptedMuMap_injective N a
  rw [map_nsmul, hv]
  exact hc

/-- Polynomial homogeneity of the integral coefficients in named cycles. -/
theorem mu_coordinates_homogeneous (N a D q : ℕ) (hqD : q ≤ D)
    {x v : A (a + 1)} (hv : adaptedMuMap N a v = x)
    (hp : eraseAuxiliary a v = v)
    (hx : ∀ s, ((chainBasis (a + 1)).repr x s).IsHomogeneous D)
    (hq : x ∈ koszulDegree (a + 1) q) :
    ∀ s, ((chainBasis (a + 1)).repr v s).IsHomogeneous (D - q) := by
  apply coefficients_homogeneous_of_polynomialEuler
  exact (mu_coordinates_euler N a D q hqD hv hp
    (polynomialEuler_of_coefficients_homogeneous _ _ hx) (exteriorEuler_eq_nsmul hq)).1

/-- The polynomial/exterior standard bases agree under the finite-function coordinate change. -/
theorem toPi_chainBasis (n : ℕ) (s : Finset (Fin n)) :
    PiCoordinates.toPi n (chainBasis n s) =
      (Pi.basisFun (R n) (Fin n)).ExteriorAlgebra s := by
  simp only [chainBasis, ExteriorAlgebra.basis_apply, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact PiCoordinates.toPi_xi n _

/-- The coordinate change preserves every polynomial coefficient of an exterior chain. -/
theorem repr_toPi (n : ℕ) (x : A n) (s : Finset (Fin n)) :
    (Pi.basisFun (R n) (Fin n)).ExteriorAlgebra.repr (PiCoordinates.toPi n x) s =
      (chainBasis n).repr x s := by
  classical
  conv_lhs => rw [← (chainBasis n).sum_repr x]
  simp only [map_sum, map_smul, toPi_chainBasis, Module.Basis.repr_self,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  simp

/-- Exterior Euler multiplies each exterior coordinate by its cardinality. -/
theorem repr_exteriorEuler (n : ℕ) (x : A n) (s : Finset (Fin n)) :
    (chainBasis n).repr (exteriorEuler n x) s = s.card • (chainBasis n).repr x s := by
  classical
  have he : ((chainBasis n).coord s).comp (exteriorEuler n) =
      s.card • (chainBasis n).coord s := by
    apply (chainBasis n).ext
    intro t
    rw [LinearMap.comp_apply, exteriorEuler_eq_nsmul (chainBasis_mem_degree n t), map_nsmul]
    by_cases h : t = s
    · simp [h]
    · simp [Ne.symm h]
  exact LinearMap.congr_fun he x

/-- An exterior Euler eigenvector has no coordinates of a different cardinality. -/
theorem coordinate_eq_zero_of_exteriorEuler (n q : ℕ) {x : A n}
    (hx : exteriorEuler n x = q • x) (s : Finset (Fin n)) (hs : s.card ≠ q) :
    (chainBasis n).repr x s = 0 := by
  by_contra hc
  have he := congrArg (fun y => (chainBasis n).repr y s) hx
  rw [repr_exteriorEuler, map_nsmul, Finsupp.nsmul_apply, nsmul_eq_mul, nsmul_eq_mul] at he
  exact hs (Nat.cast_inj.mp (mul_right_cancel₀ hc he))

/-- UEI-017 in the same finite-function coordinates returned by the integral
existence-and-uniqueness theorem. This applies to every actual coordinate witness. -/
theorem pi_mu_coordinates_homogeneous (N a D q : ℕ) (hqD : q ≤ D)
    {x : A (a + 1)} {w : PiCoordinates.PiA (a + 1)}
    (hw : ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin' w = PiCoordinates.toPi (a + 1) x)
    (hp : ExteriorAlgebra.map (eraseCoordinate 0) w = w)
    (hx : ∀ s, ((chainBasis (a + 1)).repr x s).IsHomogeneous D)
    (hq : x ∈ koszulDegree (a + 1) q) :
    (∀ s, ((Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr w s).IsHomogeneous
      (D - q)) ∧
    (∀ s, s.card ≠ q →
      (Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr w s = 0) := by
  let v : A (a + 1) := (PiCoordinates.toPi (a + 1)).symm w
  have hv : adaptedMuMap N a v = x := by
    simp only [adaptedMuMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, v,
      AlgEquiv.apply_symm_apply, hw, AlgEquiv.symm_apply_apply]
  have hpv : eraseAuxiliary a v = v := by
    simp only [eraseAuxiliary, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, v,
      AlgEquiv.apply_symm_apply, hp]
  have hrepr (s : Finset (Fin (a + 1))) :
      (Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr w s =
        (chainBasis (a + 1)).repr v s := by
    simpa only [v, AlgEquiv.apply_symm_apply] using repr_toPi (a + 1) v s
  constructor
  · intro s
    rw [hrepr]
    exact mu_coordinates_homogeneous N a D q hqD hv hpv hx hq s
  · intro s hs
    rw [hrepr]
    exact coordinate_eq_zero_of_exteriorEuler (a + 1) q
      (mu_coordinates_euler N a D q hqD hv hpv
        (polynomialEuler_of_coefficients_homogeneous _ _ hx) (exteriorEuler_eq_nsmul hq)).2 s hs

/-- UEI-016/017: a short-range homogeneous cycle has integral named-cycle
coordinates of coefficient degree `D-q`, supported in exterior degree `q`. -/
theorem exists_homogeneous_mu_cycle_coordinates (N a D q : ℕ) (haN : a ≤ N) (hqD : q ≤ D)
    (x : A (a + 1)) (hcycle : d N (a + 1) x = 0)
    (hx : ∀ s, ((chainBasis (a + 1)).repr x s).IsHomogeneous D)
    (hq : x ∈ koszulDegree (a + 1) q) :
    ∃ w : PiCoordinates.PiA (a + 1),
      ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin' w = PiCoordinates.toPi (a + 1) x ∧
      ExteriorAlgebra.map (eraseCoordinate 0) w = w ∧
      (∀ s, ((Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr w s).IsHomogeneous
        (D - q)) ∧
      (∀ s, s.card ≠ q →
        (Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr w s = 0) := by
  obtain ⟨w, hw, hp⟩ := exists_mu_cycle_coordinates N a haN x hcycle
  exact ⟨w, hw, hp, pi_mu_coordinates_homogeneous N a D q hqD hw hp hx hq⟩

end TorusLinkHomology.Generation
