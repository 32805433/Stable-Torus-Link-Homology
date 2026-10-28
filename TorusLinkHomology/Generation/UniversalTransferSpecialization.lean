import TorusLinkHomology.Generation.UniversalTransferAlgebra
import TorusLinkHomology.Generation.TailSeries

/-!
# Specialization of the universal transfer algebra

ET-13 sends universal deficit-indexed coefficients to actual polynomial
coefficients, with reflection at the stated upper exponent bounds. Thus
all convolution identities are finite polynomial identities.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.UniversalTransferSpecialization

open CoefficientComplex

/-- Coefficients in decreasing exponent order, zero beyond the upper bound. -/
def reversedCoeff {B : Type*} [Semiring B] (b : ℕ) (p : Polynomial B) (i : ℕ) : B :=
  if i ≤ b then p.coeff (b - i) else 0

theorem coeff_reflect_of_degree_le {B : Type*} [Semiring B] (b : ℕ) (p : Polynomial B)
    (hp : p.natDegree ≤ b) (i : ℕ) : (p.reflect b).coeff i = reversedCoeff b p i := by
  rw [Polynomial.coeff_reflect, reversedCoeff]
  split_ifs with hi
  · rw [Polynomial.revAt_le hi]
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hi)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hp.trans_lt (Nat.lt_of_not_ge hi))

theorem reflect_pow_of_degree_le {B : Type*} [Semiring B]
    (p : Polynomial B) (b N : ℕ) (hp : p.natDegree ≤ b) :
    (p ^ N).reflect (N * b) = (p.reflect b) ^ N := by
  induction N with
  | zero => simp [Polynomial.reflect_one]
  | succ N ih =>
    rw [pow_succ, Nat.succ_mul,
      Polynomial.reflect_mul _ _ (Polynomial.natDegree_pow_le_of_le N hp) hp, ih, pow_succ]

theorem polynomialEuler_natDegree_le {B : Type*} [Semiring B] (p : Polynomial B) :
    (TailSeries.polynomialEuler p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [TailSeries.coeff_polynomialEuler, Polynomial.coeff_eq_zero_of_natDegree_lt hi, smul_zero]

/-- Reversing polynomial Euler differentiation gives the shifted Euler operator. -/
theorem reflectedEuler {B : Type*} [Ring B] (b : ℕ) (p : Polynomial B)
    (hp : p.natDegree ≤ b) :
    ((TailSeries.polynomialEuler p).reflect b : PowerSeries B) =
      CoefficientSeries.shiftedEuler (b : ℤ) (p.reflect b) := by
  ext i
  simp only [Polynomial.coeff_coe, Polynomial.coeff_reflect, TailSeries.coeff_polynomialEuler,
    CoefficientSeries.coeff_shiftedEuler]
  by_cases hi : i ≤ b
  · rw [Polynomial.revAt_le hi, ← Nat.cast_sub hi, natCast_zsmul]
  · have hz : p.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (hp.trans_lt (Nat.lt_of_not_ge hi))
    rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hi), hz, smul_zero, smul_zero]

/-- The actual polynomial `V=(E^N)_{≤ell}` over the coefficient ring. -/
def lowerPolynomial (N r ell : ℕ) : Polynomial (CoefficientComplex.R r) :=
  TailSeries.finitePolynomial ell (G N r)

@[simp] theorem coeff_lowerPolynomial (N r ell j : ℕ) :
    (lowerPolynomial N r ell).coeff j = if j ≤ ell then G N r j else 0 := by
  classical
  simp only [lowerPolynomial, TailSeries.finitePolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.lt_succ_iff]

theorem lowerPolynomial_natDegree_le (N r ell : ℕ) :
    (lowerPolynomial N r ell).natDegree ≤ ell := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_lowerPolynomial, if_neg (Nat.not_le.mpr hj)]

/-- The actual even coefficient specialization. -/
def evenMap (N r ell : ℕ) : UniversalTransfer.R →ₐ[ℚ] CoefficientComplex.R r :=
  MvPolynomial.aeval (Sum.elim (reversedCoeff r (E r))
    (fun j => if j ≤ ell then G N r (ell - j) else 0))

@[simp] theorem evenMap_y (N r ell i : ℕ) :
    evenMap N r ell (UniversalTransfer.y i) = reversedCoeff r (E r) i := by
  simp [evenMap, UniversalTransfer.y]

@[simp] theorem evenMap_v (N r ell j : ℕ) :
    evenMap N r ell (UniversalTransfer.v j) = if j ≤ ell then G N r (ell - j) else 0 := by
  simp [evenMap, UniversalTransfer.v]

/-- Reflection at the coefficient-ring level, also usable for polynomial quotient naturality. -/
theorem evenMap_ySeries (N r ell : ℕ) :
    PowerSeries.map (evenMap N r ell).toRingHom UniversalTransfer.ySeries =
      ((E r).reflect r : PowerSeries (CoefficientComplex.R r)) := by
  ext i : 1
  rw [PowerSeries.coeff_map, UniversalTransfer.ySeries, PowerSeries.coeff_mk,
    Polynomial.coeff_coe, coeff_reflect_of_degree_le _ _ (E_natDegree_le r)]
  exact evenMap_y N r ell i

theorem evenMap_vSeries (N r ell : ℕ) :
    PowerSeries.map (evenMap N r ell).toRingHom UniversalTransfer.vSeries =
      ((lowerPolynomial N r ell).reflect ell : PowerSeries (CoefficientComplex.R r)) := by
  ext j : 1
  rw [PowerSeries.coeff_map, UniversalTransfer.vSeries, PowerSeries.coeff_mk,
    Polynomial.coeff_coe, coeff_reflect_of_degree_le _ _ (lowerPolynomial_natDegree_le N r ell)]
  change evenMap N r ell (UniversalTransfer.v j) = _
  rw [evenMap_v, reversedCoeff]
  split_ifs with hj
  · rw [coeff_lowerPolynomial, if_pos (Nat.sub_le _ _)]
  · rfl

/-- The same coefficient map viewed inside the actual exterior algebra. -/
def evenChainMap (N r ell : ℕ) : UniversalTransfer.R →+* CoefficientComplex.A r :=
  (algebraMap (CoefficientComplex.R r) (CoefficientComplex.A r)).comp (evenMap N r ell).toRingHom

/-- The lower polynomial inside the actual chain algebra. -/
def lowerChainPolynomial (N r ell : ℕ) : Polynomial (CoefficientComplex.A r) :=
  (lowerPolynomial N r ell).map (algebraMap (CoefficientComplex.R r) (CoefficientComplex.A r))

@[simp] theorem coeff_lowerChainPolynomial (N r ell j : ℕ) :
    (lowerChainPolynomial N r ell).coeff j = TailSeries.V N r ell j := by
  simp only [lowerChainPolynomial, Polynomial.coeff_map, coeff_lowerPolynomial, TailSeries.V]
  split_ifs <;> simp

theorem lowerChainPolynomial_natDegree_le (N r ell : ℕ) :
    (lowerChainPolynomial N r ell).natDegree ≤ ell :=
  Polynomial.natDegree_map_le.trans (lowerPolynomial_natDegree_le N r ell)

theorem scalarE_natDegree_le (r : ℕ) : (TailSeries.scalarE r).natDegree ≤ r :=
  Polynomial.natDegree_map_le.trans (E_natDegree_le r)

theorem map_ySeries (N r ell : ℕ) :
    PowerSeries.map (evenChainMap N r ell) UniversalTransfer.ySeries =
      ((TailSeries.scalarE r).reflect r : PowerSeries (CoefficientComplex.A r)) := by
  ext i
  rw [PowerSeries.coeff_map, UniversalTransfer.ySeries, PowerSeries.coeff_mk,
    Polynomial.coeff_coe, coeff_reflect_of_degree_le _ _ (scalarE_natDegree_le r)]
  simp [evenChainMap, reversedCoeff, TailSeries.scalarE]
  split_ifs <;> simp

theorem map_vSeries (N r ell : ℕ) :
    PowerSeries.map (evenChainMap N r ell) UniversalTransfer.vSeries =
      ((lowerChainPolynomial N r ell).reflect ell : PowerSeries (CoefficientComplex.A r)) := by
  ext j
  rw [PowerSeries.coeff_map, UniversalTransfer.vSeries, PowerSeries.coeff_mk,
    Polynomial.coeff_coe, coeff_reflect_of_degree_le _ _ (lowerChainPolynomial_natDegree_le N r ell)]
  simp [evenChainMap, reversedCoeff, lowerChainPolynomial]
  split_ifs <;> simp

/-- Specialization of the universal power coefficient uses reflection at `Nr`. -/
theorem evenChainMap_g (N r ell i : ℕ) :
    evenChainMap N r ell (UniversalTransfer.g N i) =
      if i ≤ N * r then algebraMap (CoefficientComplex.R r) (CoefficientComplex.A r)
        (G N r (N * r - i)) else 0 := by
  have h := congrArg (fun F : PowerSeries (CoefficientComplex.A r) => F.coeff i)
    (congrArg (fun F : PowerSeries (CoefficientComplex.A r) => F ^ N) (map_ySeries N r ell))
  rw [← map_pow] at h
  simp only [PowerSeries.coeff_map] at h
  rw [← Polynomial.coe_pow, ← reflect_pow_of_degree_le _ _ _ (scalarE_natDegree_le r),
    Polynomial.coeff_coe, coeff_reflect_of_degree_le _ _
      (Polynomial.natDegree_pow_le_of_le N (scalarE_natDegree_le r))] at h
  simpa only [reversedCoeff, TailSeries.scalarE, ← Polynomial.map_pow,
    Polynomial.coeff_map, G, UniversalTransfer.g] using h

private theorem reflect_nsmul {B : Type*} [Semiring B] (p : Polynomial B) (b n : ℕ) :
    (n • p).reflect b = n • p.reflect b := by
  ext i
  simp [Polynomial.coeff_reflect]

private theorem coe_nsmul {B : Type*} [Semiring B] (p : Polynomial B) (n : ℕ) :
    (n • p : Polynomial B) = n • (p : PowerSeries B) := by
  exact (Polynomial.coeToPowerSeries.ringHom.map_nsmul n p)

private theorem coe_sub_noncomm {B : Type*} [Ring B] (p q : Polynomial B) :
    (p - q : Polynomial B) = (p : PowerSeries B) - (q : PowerSeries B) := by
  ext i
  simp only [Polynomial.coeff_coe, map_sub, Polynomial.coeff_sub]

/-- Reflection of the literal Euler expression uses the sum of the two upper bounds. -/
theorem reflected_polynomialOperator (N r b : ℕ) (Y : Polynomial (CoefficientComplex.A r))
    (hY : Y.natDegree ≤ b) :
    ((TailSeries.polynomialOperator N r Y).reflect (r + b) : PowerSeries (CoefficientComplex.A r)) =
      ((TailSeries.scalarE r).reflect r : PowerSeries (CoefficientComplex.A r)) *
        CoefficientSeries.shiftedEuler (b : ℤ) (Y.reflect b : PowerSeries (CoefficientComplex.A r)) -
      N • (CoefficientSeries.shiftedEuler (r : ℤ) ((TailSeries.scalarE r).reflect r : PowerSeries (CoefficientComplex.A r)) *
        (Y.reflect b : PowerSeries (CoefficientComplex.A r))) := by
  rw [TailSeries.polynomialOperator, Polynomial.reflect_sub, reflect_nsmul,
    Polynomial.reflect_mul _ _ (scalarE_natDegree_le r) ((polynomialEuler_natDegree_le Y).trans hY),
    Polynomial.reflect_mul _ _ ((polynomialEuler_natDegree_le _).trans (scalarE_natDegree_le r)) hY]
  simp only [coe_sub_noncomm, coe_nsmul, Polynomial.coe_mul,
    reflectedEuler _ _ hY, reflectedEuler _ _ (scalarE_natDegree_le r)]

theorem polynomialOperator_natDegree_le (N r b : ℕ) (Y : Polynomial (CoefficientComplex.A r))
    (hY : Y.natDegree ≤ b) : (TailSeries.polynomialOperator N r Y).natDegree ≤ r + b := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [TailSeries.coeff_polynomialOperator]
  apply TailSeries.eulerOperator_support N r b Y.coeff
  · intro k hk
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hY.trans_lt hk)
  · omega

private theorem map_shiftedEuler {S T : Type*} [Ring S] [Ring T]
    (f : S →+* T) (b : ℤ) (Y : PowerSeries S) :
    PowerSeries.map f (CoefficientSeries.shiftedEuler b Y) =
      CoefficientSeries.shiftedEuler b (PowerSeries.map f Y) := by
  ext i
  simp only [PowerSeries.coeff_map, CoefficientSeries.coeff_shiftedEuler, map_zsmul]

/-- Specialization of the free `Q` equation to the reflected actual polynomial equation. -/
theorem evenChainMap_qEquation (N r ell h : ℕ) (hell : ell ≤ N * r) :
    evenChainMap N r ell (UniversalTransfer.qEquation N (N * r - ell) h) =
      if h ≤ ell + r then invNat r N •
        TailSeries.eulerOperator N r (TailSeries.V N r ell) (ell + r - h) else 0 := by
  have hbound : N * r = ell + (N * r - ell) := by omega
  have hs := congrArg (PowerSeries.map (evenChainMap N r ell))
    (UniversalTransfer.qEquation_series N (N * r - ell) r ell hbound)
  rw [map_mul, map_sub, map_nsmul, map_mul, map_mul,
    map_shiftedEuler, map_shiftedEuler, map_ySeries, map_vSeries,
    ← reflected_polynomialOperator _ _ _ _ (lowerChainPolynomial_natDegree_le N r ell)] at hs
  have hc : PowerSeries.map (evenChainMap N r ell)
      (PowerSeries.C (MvPolynomial.C ((N : ℚ)⁻¹))) =
      PowerSeries.C (algebraMap (CoefficientComplex.R r) (CoefficientComplex.A r) (invNat r N)) := by
    simp [evenChainMap, invNat, evenMap]
  rw [hc] at hs
  have h' := congrArg (fun F : PowerSeries (CoefficientComplex.A r) => F.coeff h) hs
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    Polynomial.coeff_coe] at h'
  rw [coeff_reflect_of_degree_le _ _
    (polynomialOperator_natDegree_le N r ell _ (lowerChainPolynomial_natDegree_le N r ell))] at h'
  have hV : (lowerChainPolynomial N r ell).coeff = TailSeries.V N r ell :=
    funext (coeff_lowerChainPolynomial N r ell)
  simp only [reversedCoeff, TailSeries.coeff_polynomialOperator, hV, apply_ite, mul_zero,
    ← Algebra.smul_def] at h'
  by_cases hh : h ≤ ell + r <;> simpa only [Nat.add_comm r ell, hh, ↓reduceIte] using h'

@[simp] theorem evenChainMap_v (N r ell j : ℕ) :
    evenChainMap N r ell (UniversalTransfer.v j) =
      if j ≤ ell then algebraMap (CoefficientComplex.R r) (CoefficientComplex.A r)
        (G N r (ell - j)) else 0 := by
  simp only [evenChainMap, RingHom.comp_apply]
  change algebraMap (CoefficientComplex.R r) (CoefficientComplex.A r)
    (evenMap N r ell (UniversalTransfer.v j)) = _
  rw [evenMap_v]
  split_ifs <;> simp

theorem evenChainMap_shiftedV (N r ell i : ℕ) (hell : ell ≤ N * r) :
    evenChainMap N r ell (UniversalTransfer.shiftedV (N * r - ell) i) =
      if i ≤ N * r then TailSeries.V N r ell (N * r - i) else 0 := by
  unfold UniversalTransfer.shiftedV
  by_cases hi : i ≤ N * r
  · rw [if_pos hi]
    by_cases hm : N * r - ell ≤ i
    · rw [if_pos hm, evenChainMap_v, if_pos (by omega), TailSeries.V, if_pos (by omega)]
      congr 2
      omega
    · rw [if_neg hm, map_zero, TailSeries.V, if_neg (by omega)]
  · rw [if_neg hi, if_pos (by omega), evenChainMap_v, if_neg (by omega)]

/-- The image of the deficit-indexed universal `A_i` generator. -/
def oddAImage (N r ell : ℕ) : ℕ → CoefficientComplex.A r :=
  reversedCoeff (N * r) (TailSeries.cPolynomial N r ell)

/-- The image of the deficit-indexed universal `Q_h` generator. -/
def oddQImage (N r ell : ℕ) : ℕ → CoefficientComplex.A r :=
  reversedCoeff (ell + r) (TailSeries.qPolynomial N r ell)

/-- The actual `A` generator equation after specialization. -/
theorem d_oddAImage (N r ell i : ℕ) (hell : ell ≤ N * r) :
    CoefficientComplex.d N r ell (oddAImage N r ell i) =
      evenChainMap N r ell (UniversalTransfer.equation N (N * r - ell) (Sum.inl i)) := by
  rw [UniversalTransfer.equation, map_sub, evenChainMap_shiftedV _ _ _ _ hell, evenChainMap_g]
  unfold oddAImage reversedCoeff
  split_ifs with hi
  · rw [TailSeries.coeff_cPolynomial, TailSeries.d_C _ _ _ _ hell]
  · rw [map_zero, sub_zero]

/-- The actual `Q` generator equation after specialization. -/
theorem d_oddQImage (N r ell h : ℕ) (hell : ell ≤ N * r) :
    CoefficientComplex.d N r ell (oddQImage N r ell h) =
      evenChainMap N r ell (UniversalTransfer.equation N (N * r - ell) (Sum.inr h)) := by
  rw [UniversalTransfer.equation, evenChainMap_qEquation _ _ _ _ hell]
  unfold oddQImage reversedCoeff
  split_ifs
  · rw [TailSeries.coeff_qPolynomial, TailSeries.d_Q]
  · exact map_zero _

theorem oddAImage_mem_degree_one (N r ell i : ℕ) :
    oddAImage N r ell i ∈ ExteriorAlgebra.exteriorPower (CoefficientComplex.R r) 1
      (CoefficientComplex.V r) := by
  unfold oddAImage reversedCoeff
  split_ifs
  · rw [TailSeries.coeff_cPolynomial]
    exact TailSeries.C_mem_degree_one _ _ _ _
  · exact Submodule.zero_mem _

theorem oddQImage_mem_degree_one (N r ell h : ℕ) :
    oddQImage N r ell h ∈ ExteriorAlgebra.exteriorPower (CoefficientComplex.R r) 1
      (CoefficientComplex.V r) := by
  unfold oddQImage reversedCoeff
  split_ifs
  · rw [TailSeries.coeff_qPolynomial]
    exact TailSeries.Q_mem_degree_one _ _ _ _
  · exact Submodule.zero_mem _

/-- Both actual odd coefficient families, with their original distinction retained. -/
def oddImage (N r ell : ℕ) : ℕ ⊕ ℕ → CoefficientComplex.A r :=
  Sum.elim (oddAImage N r ell) (oddQImage N r ell)

def oddVector (N r ell : ℕ) (i : ℕ ⊕ ℕ) : CoefficientComplex.V r :=
  ExteriorAlgebra.ιInv (oddImage N r ell i)

@[simp] theorem iota_oddVector (N r ell : ℕ) (i : ℕ ⊕ ℕ) :
    ExteriorAlgebra.ι (CoefficientComplex.R r) (oddVector N r ell i) = oddImage N r ell i := by
  have hi : oddImage N r ell i ∈ ExteriorAlgebra.exteriorPower (CoefficientComplex.R r) 1
      (CoefficientComplex.V r) := by
    cases i with
    | inl i => exact oddAImage_mem_degree_one N r ell i
    | inr h => exact oddQImage_mem_degree_one N r ell h
  change oddImage N r ell i ∈ LinearMap.range (ExteriorAlgebra.ι (CoefficientComplex.R r)) ^ 1 at hi
  rw [pow_one] at hi
  obtain ⟨z, hz⟩ := hi
  rw [oddVector, ← hz, ExteriorAlgebra.ι_leftInverse]

/-- The semilinear map on the free odd-generator module. -/
def vectorMap (N r ell : ℕ) :
    UniversalTransfer.V →ₛₗ[(evenMap N r ell).toRingHom] CoefficientComplex.V r :=
  (Finsupp.linearCombination (CoefficientComplex.R r) (oddVector N r ell)).comp
    (Finsupp.mapRange.linearMap (evenMap N r ell).toRingHom.toSemilinearMap)

@[simp] theorem vectorMap_single (N r ell : ℕ) (i : ℕ ⊕ ℕ) (c : UniversalTransfer.R) :
    vectorMap N r ell (Finsupp.single i c) = evenMap N r ell c • oddVector N r ell i := by
  change Finsupp.linearCombination (CoefficientComplex.R r) (oddVector N r ell)
    (Finsupp.mapRange (evenMap N r ell) (map_zero _) (Finsupp.single i c)) = _
  rw [Finsupp.mapRange_single, Finsupp.linearCombination_single]

/-- The actual specialization ring map from the free transfer exterior algebra. -/
def specialize (N r ell : ℕ) : UniversalTransfer.A →+* CoefficientComplex.A r :=
  ExteriorAlgebra.mapOfSemilinear (evenMap N r ell).toRingHom (vectorMap N r ell)

@[simp] theorem specialize_scalar (N r ell : ℕ) (c : UniversalTransfer.R) :
    specialize N r ell (algebraMap UniversalTransfer.R UniversalTransfer.A c) =
      evenChainMap N r ell c := by
  exact ExteriorAlgebra.mapOfSemilinear_algebraMap _ _ _

theorem specialize_smul (N r ell : ℕ) (c : UniversalTransfer.R) (x : UniversalTransfer.A) :
    specialize N r ell (c • x) = evenMap N r ell c • specialize N r ell x :=
  ExteriorAlgebra.mapOfSemilinear_smul _ _ _ _

@[simp] theorem specialize_oddA (N r ell i : ℕ) :
    specialize N r ell (UniversalTransfer.oddA i) = oddAImage N r ell i := by
  rw [specialize, UniversalTransfer.oddA, ExteriorAlgebra.mapOfSemilinear_iota,
    vectorMap_single, map_one, one_smul, iota_oddVector]
  rfl

@[simp] theorem specialize_oddQ (N r ell h : ℕ) :
    specialize N r ell (UniversalTransfer.oddQ h) = oddQImage N r ell h := by
  rw [specialize, UniversalTransfer.oddQ, ExteriorAlgebra.mapOfSemilinear_iota,
    vectorMap_single, map_one, one_smul, iota_oddVector]
  rfl

/-- The two actual generator equations give equality of the differential functionals. -/
theorem functional_oddVector (N r ell : ℕ) (hell : ell ≤ N * r) (i : ℕ ⊕ ℕ) :
    differentialFunctional N r ell (oddVector N r ell i) =
      evenMap N r ell (UniversalTransfer.equation N (N * r - ell) i) := by
  apply (ExteriorAlgebra.algebraMap_inj (M := CoefficientComplex.V r) _ _).mp
  have he : CoefficientComplex.d N r ell (oddImage N r ell i) =
      evenChainMap N r ell (UniversalTransfer.equation N (N * r - ell) i) := by
    cases i with
    | inl i => exact d_oddAImage N r ell i hell
    | inr h => exact d_oddQImage N r ell h hell
  rw [← iota_oddVector N r ell i] at he
  change CliffordAlgebra.contractLeft (differentialFunctional N r ell)
    (ExteriorAlgebra.ι (R r) (oddVector N r ell i)) =
    algebraMap (R r) (CoefficientComplex.A r)
      (evenMap N r ell (UniversalTransfer.equation N (N * r - ell) i)) at he
  rw [CliffordAlgebra.contractLeft_ι] at he
  exact he

theorem functional_vectorMap (N r ell : ℕ) (hell : ell ≤ N * r) (z : UniversalTransfer.V) :
    differentialFunctional N r ell (vectorMap N r ell z) =
      evenMap N r ell (UniversalTransfer.functional N (N * r - ell) z) := by
  induction z using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add i c z _ _ ih =>
    simp only [map_add, vectorMap_single, map_smul, functional_oddVector _ _ _ hell,
      UniversalTransfer.functional, Finsupp.linearCombination_single, smul_eq_mul,
      map_mul, ih]

/-- ET-13: the literal polynomial-coefficient specialization is a chain map. -/
theorem d_specialize (N r ell : ℕ) (hell : ell ≤ N * r) (x : UniversalTransfer.A) :
    CoefficientComplex.d N r ell (specialize N r ell x) =
      specialize N r ell (UniversalTransfer.d N (N * r - ell) x) := by
  exact ExteriorAlgebra.contractLeft_mapOfSemilinear (evenMap N r ell).toRingHom (vectorMap N r ell)
    (UniversalTransfer.functional N (N * r - ell)) (differentialFunctional N r ell)
    (functional_vectorMap N r ell hell) x

end TorusLinkHomology.UniversalTransferSpecialization
