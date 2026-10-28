import TorusLinkHomology.Generation.CoefficientComplex
import DGA.ExteriorMap
import DGA.ExteriorScalarChange

/-!
# The comparison map decreasing the first coefficient index

The map J fixes polynomial coefficients and sends each initial odd generator
to the extended generator with the same absolute index in the neighboring
coefficient complex. Its construction uses the degree-one projection of the
exterior algebra, so no new odd generators are introduced.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientComplex


/-- Setting the last coefficient variable to zero. -/
def reduceCoefficients (r : ℕ) : R (r + 1) →ₐ[ℚ] R r :=
  MvPolynomial.aeval (fun i : Fin (r + 1) =>
    if h : i.val < r then e r ⟨i.val, h⟩ else 0)

@[simp] theorem reduceCoefficients_e_castSucc (r : ℕ) (i : Fin r) :
    reduceCoefficients r (e (r + 1) i.castSucc) = e r i := by
  simp [reduceCoefficients, e]

@[simp] theorem reduceCoefficients_e_last (r : ℕ) :
    reduceCoefficients r (e (r + 1) (Fin.last r)) = 0 := by
  simp [reduceCoefficients, e]

/-- Reduction of the coefficient polynomial agrees with decreasing its degree. -/
theorem reduce_E (r : ℕ) :
    (E (r + 1)).map (reduceCoefficients r).toRingHom = E r := by
  classical
  simp [E, Polynomial.map_sum, Fin.sum_univ_castSucc]

/-- Reduction commutes with taking every coefficient of the N-th power. -/
@[simp] theorem reduce_G (N r j : ℕ) :
    reduceCoefficients r (G N (r + 1) j) = G N r j := by
  change (reduceCoefficients r).toRingHom ((E (r + 1) ^ N).coeff j) =
    (E r ^ N).coeff j
  rw [← Polynomial.coeff_map, Polynomial.map_pow, reduce_E]

/-- The vector underlying an extended degree-one generator. -/
def tailVector (N r ell j : ℕ) : V r :=
  ExteriorAlgebra.ιInv (tail N r ell j)

@[simp] theorem iota_tailVector (N r ell j : ℕ) :
    ExteriorAlgebra.ι (R r) (tailVector N r ell j) = tail N r ell j := by
  have h := tail_mem_degree_one N r ell j
  change tail N r ell j ∈ LinearMap.range (ExteriorAlgebra.ι (R r)) ^ 1 at h
  rw [pow_one] at h
  obtain ⟨v, hv⟩ := h
  unfold tailVector
  rw [← hv, ExteriorAlgebra.ι_leftInverse]

theorem differentialFunctional_tailVector (N r ell j : ℕ) (hj : ell < j) :
    differentialFunctional N r ell (tailVector N r ell j) = G N r j := by
  apply (ExteriorAlgebra.algebraMap_inj (M := V r) _ _).mp
  have h := d_tail N r ell j hj
  rw [← iota_tailVector N r ell j] at h
  change CliffordAlgebra.contractLeft (Q := 0) (differentialFunctional N r ell)
    (ExteriorAlgebra.ι (R r) (tailVector N r ell j)) = _ at h
  simpa only [CliffordAlgebra.contractLeft_ι] using h

/-- The linear map on generators underlying the comparison map J. -/
def JLinear (N r ell : ℕ) : V r →ₗ[R r] V r :=
  Finsupp.linearCombination (R r)
    (fun i : Fin r => tailVector N r (ell - 1) (ell + i.val + 1))

/-- The coefficient-preserving map from offset ell to offset ell-1. -/
def J (N r ell : ℕ) : A r →ₐ[R r] A r :=
  ExteriorAlgebra.map (JLinear N r ell)

@[simp] theorem J_xi (N r ell : ℕ) (i : Fin r) :
    J N r ell (xi r i) = tail N r (ell - 1) (ell + i.val + 1) := by
  simp [J, xi, JLinear]

theorem differentialFunctional_comp_JLinear (N r ell : ℕ) :
    (differentialFunctional N r (ell - 1)).comp (JLinear N r ell) =
      differentialFunctional N r ell := by
  apply Finsupp.lhom_ext
  intro i c
  simp only [LinearMap.comp_apply, JLinear, Finsupp.linearCombination_single, map_smul]
  rw [differentialFunctional_tailVector _ _ _ _ (by omega)]
  simp [differentialFunctional]

/-- The comparison map is a chain map. -/
theorem d_J (N r ell : ℕ) (a : A r) :
    d N r (ell - 1) (J N r ell a) = J N r ell (d N r ell a) := by
  exact ExteriorAlgebra.contractLeft_map_of_comp_eq
    (JLinear N r ell) (differentialFunctional N r (ell - 1))
    (differentialFunctional N r ell) (differentialFunctional_comp_JLinear N r ell) a

/-- Naturality for any generator in the initial coefficient interval. -/
theorem J_chi (N r ell j : ℕ) (hj : ell < j) (hjr : j ≤ ell + r) :
    J N r ell (chi r ell j) = tail N r (ell - 1) j := by
  rw [chi, dif_pos ⟨hj, hjr⟩, J_xi]
  congr 1
  change ell + (j - ell - 1) + 1 = j
  omega

/-- Naturality for the full recursively extended family. -/
theorem J_tail (N r ell j : ℕ) (hj : ell < j) :
    J N r ell (tail N r ell j) = tail N r (ell - 1) j := by
  classical
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases htop : j ≤ ell + r
    · rw [tail_eq_chi _ _ _ _ htop, J_chi _ _ _ _ hj htop]
    · have hgt : ell + r < j := Nat.lt_of_not_ge htop
      rw [tail_eq_of_gt _ _ _ _ hgt,
        tail_eq_of_gt N r (ell - 1) j (by omega)]
      simp only [map_smul, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply ih _ (by omega)
      have := i.isLt
      omega

/-- On the common initial coefficient interval, J fixes the named chains. -/
theorem J_chi_common (N r ell j : ℕ) (hj : ell < j) (hjr : j ≤ ell - 1 + r) :
    J N r ell (chi r ell j) = chi r (ell - 1) j := by
  rw [J_chi _ _ _ _ hj (by omega), tail_eq_chi _ _ _ _ hjr]

/-- A new cycle remains a cycle under the comparison map. -/
theorem J_cycle (N r ell : ℕ) {a : A r} (ha : d N r ell a = 0) :
    d N r (ell - 1) (J N r ell a) = 0 := by
  rw [d_J, ha, map_zero]

/-- The semilinear map on odd generators for reduction of the last coefficient. -/
def rhoVector (N r ell : ℕ) :
    V (r + 1) →ₛₗ[(reduceCoefficients r).toRingHom] V r :=
  (Finsupp.linearCombination (R r)
    (fun i : Fin (r + 1) => tailVector N r ell (ell + i.val + 1))).comp
      (Finsupp.mapRange.linearMap (reduceCoefficients r).toRingHom.toSemilinearMap)

@[simp] theorem rhoVector_single (N r ell : ℕ) (i : Fin (r + 1)) (c : R (r + 1)) :
    rhoVector N r ell (Finsupp.single i c) =
      reduceCoefficients r c • tailVector N r ell (ell + i.val + 1) := by
  change Finsupp.linearCombination (R r)
    (fun i : Fin (r + 1) => tailVector N r ell (ell + i.val + 1))
    (Finsupp.mapRange (reduceCoefficients r) (map_zero _) (Finsupp.single i c)) = _
  rw [Finsupp.mapRange_single, Finsupp.linearCombination_single]

theorem differentialFunctional_rhoVector (N r ell : ℕ) (v : V (r + 1)) :
    differentialFunctional N r ell (rhoVector N r ell v) =
      reduceCoefficients r (differentialFunctional N (r + 1) ell v) := by
  have h :
      (differentialFunctional N r ell).comp (rhoVector N r ell) =
        (reduceCoefficients r).toRingHom.toSemilinearMap.comp
          (differentialFunctional N (r + 1) ell) := by
    apply Finsupp.lhom_ext
    intro i c
    simp only [LinearMap.comp_apply, rhoVector_single, map_smul]
    rw [differentialFunctional_tailVector _ _ _ _ (by omega)]
    change reduceCoefficients r c * G N r (ell + i.val + 1) =
      reduceCoefficients r (differentialFunctional N (r + 1) ell (Finsupp.single i c))
    simp [differentialFunctional]
  exact LinearMap.congr_fun h v

/-- Reduction from rank r+1 to rank r, including the coefficient-ring change. -/
def rhoSucc (N r ell : ℕ) : A (r + 1) →+* A r :=
  ExteriorAlgebra.mapOfSemilinear (reduceCoefficients r).toRingHom (rhoVector N r ell)

@[simp] theorem rhoSucc_xi (N r ell : ℕ) (i : Fin (r + 1)) :
    rhoSucc N r ell (xi (r + 1) i) = tail N r ell (ell + i.val + 1) := by
  rw [rhoSucc, xi, ExteriorAlgebra.mapOfSemilinear_iota, rhoVector_single]
  simp

@[simp] theorem rhoSucc_algebraMap (N r ell : ℕ) (c : R (r + 1)) :
    rhoSucc N r ell (algebraMap (R (r + 1)) (A (r + 1)) c) =
      algebraMap (R r) (A r) (reduceCoefficients r c) :=
  ExteriorAlgebra.mapOfSemilinear_algebraMap _ _ _

theorem rhoSucc_smul (N r ell : ℕ) (c : R (r + 1)) (a : A (r + 1)) :
    rhoSucc N r ell (c • a) = reduceCoefficients r c • rhoSucc N r ell a :=
  ExteriorAlgebra.mapOfSemilinear_smul _ _ _ _

/-- Coefficient reduction commutes with the Koszul differentials. -/
theorem d_rhoSucc (N r ell : ℕ) (a : A (r + 1)) :
    d N r ell (rhoSucc N r ell a) = rhoSucc N r ell (d N (r + 1) ell a) :=
  ExteriorAlgebra.contractLeft_mapOfSemilinear _ _ _ _
    (differentialFunctional_rhoVector N r ell) a

theorem rhoSucc_chi (N r ell j : ℕ) (hj : ell < j) (hjr : j ≤ ell + (r + 1)) :
    rhoSucc N r ell (chi (r + 1) ell j) = tail N r ell j := by
  rw [chi, dif_pos ⟨hj, hjr⟩, rhoSucc_xi]
  congr 1
  change ell + (j - ell - 1) + 1 = j
  omega

@[simp] theorem reduce_invNat (r j : ℕ) :
    reduceCoefficients r (invNat (r + 1) j) = invNat r j := by
  simp [invNat]

/-- Reduction preserves every recursively extended generator above the offset. -/
theorem rhoSucc_tail (N r ell j : ℕ) (hj : ell < j) :
    rhoSucc N r ell (tail N (r + 1) ell j) = tail N r ell j := by
  classical
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases htop : j ≤ ell + (r + 1)
    · rw [tail_eq_chi _ _ _ _ htop, rhoSucc_chi _ _ _ _ hj htop]
    · have hgt : ell + (r + 1) < j := Nat.lt_of_not_ge htop
      rw [tail_eq_of_gt _ _ _ _ hgt, rhoSucc_smul, reduce_invNat,
        tail_eq_of_gt N r ell j (by omega), map_sum]
      simp only [rhoSucc_smul]
      rw [Fin.sum_univ_castSucc]
      simp only [map_mul, map_sub, map_natCast, reduceCoefficients_e_castSucc,
        reduceCoefficients_e_last, mul_zero, zero_smul, add_zero, Fin.val_castSucc]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply ih _ (by omega)
      have := i.isLt
      omega

end TorusLinkHomology.CoefficientComplex
