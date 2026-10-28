import TorusLinkHomology.Generation.UniversalTransferSpecialization

/-!
# The closed universal P series

Series indices are exponent deficits. The C series has upper exponent Nr,
whereas Q has upper exponent ell+r. Thus multiplying Q by X^m, with
Nr=ell+m, puts both terms of P at the common upper exponent (N+1)r.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientSeries

variable {B : Type*} [Ring B]

/-- Coefficientwise Euler differentiation commutes with coefficient homomorphisms. -/
theorem map_shiftedEuler {T : Type*} [Ring T] (f : B →+* T) (b : ℤ)
    (F : PowerSeries B) :
    PowerSeries.map f (shiftedEuler b F) = shiftedEuler b (PowerSeries.map f F) := by
  ext i
  simp only [PowerSeries.coeff_map, coeff_shiftedEuler, map_zsmul]

theorem shiftedEuler_sub (b : ℤ) (F G : PowerSeries B) :
    shiftedEuler b (F - G) = shiftedEuler b F - shiftedEuler b G := by
  ext i
  simp only [coeff_shiftedEuler, map_sub, smul_sub]

/-- Raising the upper bound and shifting the deficit by the same amount cancel. -/
theorem shiftedEuler_X_pow_mul (b : ℤ) (m : ℕ) (F : PowerSeries B) :
    shiftedEuler (b + (m : ℤ)) (PowerSeries.X ^ m * F) =
      PowerSeries.X ^ m * shiftedEuler b F := by
  ext i
  simp only [coeff_shiftedEuler, PowerSeries.coeff_X_pow_mul']
  split_ifs with hi
  · rw [Nat.cast_sub hi]
    congr 1
    ring
  · simp

/-- The Euler expression with explicit upper exponents for both inputs. -/
def expression (N : ℕ) (r b : ℤ) (U F : PowerSeries B) : PowerSeries B :=
  U * shiftedEuler b F - N • (shiftedEuler r U * F)

theorem expression_sub (N : ℕ) (r b : ℤ) (U F G : PowerSeries B) :
    expression N r b U (F - G) = expression N r b U F - expression N r b U G := by
  simp only [expression, shiftedEuler_sub, mul_sub, smul_sub]
  abel

/-- Aligning the second input's upper exponent commutes with the Euler expression. -/
theorem expression_X_pow_mul (N : ℕ) (r b : ℤ) (m : ℕ) (U F : PowerSeries B) :
    expression N r (b + (m : ℤ)) U (PowerSeries.X ^ m * F) =
      PowerSeries.X ^ m * expression N r b U F := by
  rw [expression, shiftedEuler_X_pow_mul, expression, mul_sub, mul_smul_comm]
  congr 1
  · rw [← mul_assoc, ← PowerSeries.X_pow_mul, mul_assoc]
  · rw [← mul_assoc, ← PowerSeries.X_pow_mul, mul_assoc]

theorem map_expression {T : Type*} [Ring T] (f : B →+* T) (N : ℕ)
    (r b : ℤ) (U F : PowerSeries B) :
    PowerSeries.map f (expression N r b U F) =
      expression N r b (PowerSeries.map f U) (PowerSeries.map f F) := by
  simp only [expression, map_sub, map_mul, map_nsmul, map_shiftedEuler]

section CommRing

variable {K : Type*} [CommRing K]

/-- Euler's power rule in upper-exponent notation. -/
theorem shiftedEuler_pow_succ (F : PowerSeries K) (b : ℤ) (N : ℕ) :
    shiftedEuler (((N + 1 : ℕ) : ℤ) * b) (F ^ (N + 1)) =
      (N + 1) • (shiftedEuler b F * F ^ N) := by
  induction N with
  | zero => simp [shiftedEuler]
  | succ N ih =>
    rw [show ((N + 1 + 1 : ℕ) : ℤ) * b = ((N + 1 : ℕ) : ℤ) * b + b by push_cast; ring,
      pow_succ, shiftedEuler_mul, ih]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

/-- The Euler expression annihilates the N-th power of its first input. -/
theorem expression_pow (N : ℕ) (b : ℤ) (F : PowerSeries K) :
    expression N b ((N : ℤ) * b) F (F ^ N) = 0 := by
  cases N with
  | zero => simp [expression, shiftedEuler]
  | succ N =>
    rw [expression, shiftedEuler_pow_succ]
    simp only [nsmul_eq_mul, pow_succ]
    ring

end CommRing
end TorusLinkHomology.CoefficientSeries

namespace TorusLinkHomology.UniversalTransfer

/-- Embed the free scalar series coefficientwise in the free exterior algebra. -/
def scalarSeries : PowerSeries R →+* PowerSeries A := PowerSeries.map (algebraMap R A)

/-- The universal Euler expression at C's upper exponent Nr. -/
def sSeries (N r : ℕ) (F : PowerSeries A) : PowerSeries A :=
  CoefficientSeries.expression N (r : ℤ) ((N * r : ℕ) : ℤ) (scalarSeries ySeries) F

/-- The closed series P, written at the common upper exponent (N+1)r. -/
def pSeries (N m r : ℕ) : PowerSeries A :=
  N • (PowerSeries.X ^ m * qSeries) - sSeries N r cSeries

@[simp] theorem dSeries_add (N m : ℕ) (F G : PowerSeries A) :
    dSeries N m (F + G) = dSeries N m F + dSeries N m G := by
  ext i
  simp only [coeff_dSeries, map_add]

@[simp] theorem dSeries_sub (N m : ℕ) (F G : PowerSeries A) :
    dSeries N m (F - G) = dSeries N m F - dSeries N m G := by
  ext i
  simp only [coeff_dSeries, map_sub]

@[simp] theorem dSeries_nsmul (N m k : ℕ) (F : PowerSeries A) :
    dSeries N m (k • F) = k • dSeries N m F := by
  ext i
  simp only [coeff_dSeries, map_nsmul]

/-- The coefficientwise differential is linear over every free scalar series. -/
theorem dSeries_scalar_mul (N m : ℕ) (F : PowerSeries R) (G : PowerSeries A) :
    dSeries N m (scalarSeries F * G) = scalarSeries F * dSeries N m G := by
  ext i
  simp only [coeff_dSeries, PowerSeries.coeff_mul, map_sum, scalarSeries,
    PowerSeries.coeff_map]
  apply Finset.sum_congr rfl
  intro ij _
  change d N m (algebraMap R A (F.coeff ij.1) * G.coeff ij.2) = _
  simpa only [Algebra.smul_def] using (d N m).map_smul (F.coeff ij.1) (G.coeff ij.2)

theorem dSeries_X_pow_mul (N m k : ℕ) (F : PowerSeries A) :
    dSeries N m (PowerSeries.X ^ k * F) = PowerSeries.X ^ k * dSeries N m F := by
  ext i
  simp only [coeff_dSeries, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp only [map_zero]

theorem dSeries_expression (N m : ℕ) (r b : ℤ)
    (F : PowerSeries R) (G : PowerSeries A) :
    dSeries N m (CoefficientSeries.expression N r b (scalarSeries F) G) =
      CoefficientSeries.expression N r b (scalarSeries F) (dSeries N m G) := by
  rw [CoefficientSeries.expression, dSeries_sub, dSeries_scalar_mul,
    dSeries_shiftedEuler, dSeries_nsmul]
  have he : CoefficientSeries.shiftedEuler r (scalarSeries F) =
      scalarSeries (CoefficientSeries.shiftedEuler r F) :=
    (CoefficientSeries.map_shiftedEuler (algebraMap R A) r F).symm
  rw [he, dSeries_scalar_mul, CoefficientSeries.expression, he]

theorem mk_shiftedV_eq (m : ℕ) :
    PowerSeries.mk (shiftedV m) = PowerSeries.X ^ m * vSeries := by
  ext i : 1
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', vSeries, shiftedV]

/-- Multiplication by the positive integer N cancels precisely its rational inverse. -/
theorem nat_smul_dSeries_qSeries (N m r ell : ℕ) (hN : 0 < N)
    (hbound : N * r = ell + m) :
    N • dSeries N m qSeries = scalarSeries
      (CoefficientSeries.expression N (r : ℤ) (ell : ℤ) ySeries vSeries) := by
  have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hinv : (N : R) * MvPolynomial.C ((N : ℚ)⁻¹) = 1 := by
    rw [← map_natCast (MvPolynomial.C : ℚ →+* R) N, ← map_mul,
      mul_inv_cancel₀ hNQ, map_one]
  have hc : (N : PowerSeries R) * PowerSeries.C (MvPolynomial.C ((N : ℚ)⁻¹)) = 1 := by
    rw [← map_natCast (PowerSeries.C : R →+* PowerSeries R) N, ← map_mul, hinv, map_one]
  rw [dSeries_qSeries, qEquation_series N m r ell hbound]
  change N • scalarSeries _ = _
  rw [← map_nsmul, nsmul_eq_mul, ← mul_assoc, hc, one_mul]
  rfl

theorem dSeries_sSeries_cSeries (N m r ell : ℕ) (hbound : N * r = ell + m) :
    dSeries N m (sSeries N r cSeries) = scalarSeries
      (PowerSeries.X ^ m *
        CoefficientSeries.expression N (r : ℤ) (ell : ℤ) ySeries vSeries) := by
  rw [sSeries, dSeries_expression, dSeries_cSeries]
  change CoefficientSeries.expression N (r : ℤ) ((N * r : ℕ) : ℤ)
    (scalarSeries ySeries) (scalarSeries _) = _
  simp only [scalarSeries]
  rw [← CoefficientSeries.map_expression, mk_shiftedV_eq,
    CoefficientSeries.expression_sub]
  have hz : CoefficientSeries.expression N (r : ℤ) ((N * r : ℕ) : ℤ)
      ySeries (ySeries ^ N) = 0 := by
    rw [Nat.cast_mul]
    exact CoefficientSeries.expression_pow N (r : ℤ) ySeries
  rw [hz, sub_zero, hbound, Nat.cast_add, CoefficientSeries.expression_X_pow_mul]

/-- ET-09: every coefficient of the literal free P series is closed. -/
theorem dSeries_pSeries (N m r ell : ℕ) (hN : 0 < N)
    (hbound : N * r = ell + m) : dSeries N m (pSeries N m r) = 0 := by
  rw [pSeries, dSeries_sub, dSeries_nsmul, dSeries_X_pow_mul,
    ← mul_smul_comm, nat_smul_dSeries_qSeries N m r ell hN hbound,
    dSeries_sSeries_cSeries N m r ell hbound, map_mul]
  have hX : scalarSeries (PowerSeries.X ^ m) = PowerSeries.X ^ m := by
    simp [scalarSeries]
  rw [hX, sub_self]

theorem pSeries_coeff_is_cycle (N m r ell i : ℕ) (hN : 0 < N)
    (hbound : N * r = ell + m) : d N m ((pSeries N m r).coeff i) = 0 := by
  have h := congrArg (fun F : PowerSeries A => F.coeff i)
    (dSeries_pSeries N m r ell hN hbound)
  simpa only [coeff_dSeries, map_zero] using h

end TorusLinkHomology.UniversalTransfer

namespace TorusLinkHomology.UniversalTransferSpecialization

open CoefficientComplex

/-- Increasing a polynomial's reflection bound inserts precisely a deficit shift. -/
theorem reflect_add_eq_X_pow_mul {B : Type*} [Ring B] (p : Polynomial B)
    (b m : ℕ) (hp : p.natDegree ≤ b) :
    (p.reflect (b + m) : PowerSeries B) =
      PowerSeries.X ^ m * (p.reflect b : PowerSeries B) := by
  have h := Polynomial.reflect_mul (1 : Polynomial B) p (F := m) (G := b) (by simp) hp
  rw [one_mul, Polynomial.reflect_one] at h
  have h' := congrArg (fun P : Polynomial B => (P : PowerSeries B)) h
  simpa only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Nat.add_comm m b] using h'

/-- The odd C coefficients specialize to the actual polynomial, reflected at Nr. -/
theorem map_cSeries (N r ell : ℕ) :
    PowerSeries.map (specialize N r ell) UniversalTransfer.cSeries =
      ((TailSeries.cPolynomial N r ell).reflect (N * r) : PowerSeries (A r)) := by
  ext i
  rw [PowerSeries.coeff_map, UniversalTransfer.cSeries, PowerSeries.coeff_mk,
    specialize_oddA, Polynomial.coeff_coe,
    coeff_reflect_of_degree_le _ _ (TailSeries.cPolynomial_natDegree_le N r ell)]
  rfl

/-- The odd Q coefficients use their smaller original upper bound ell+r. -/
theorem map_qSeries (N r ell : ℕ) :
    PowerSeries.map (specialize N r ell) UniversalTransfer.qSeries =
      ((TailSeries.qPolynomial N r ell).reflect (ell + r) : PowerSeries (A r)) := by
  ext i
  rw [PowerSeries.coeff_map, UniversalTransfer.qSeries, PowerSeries.coeff_mk,
    specialize_oddQ, Polynomial.coeff_coe,
    coeff_reflect_of_degree_le _ _ (TailSeries.qPolynomial_natDegree_le N r ell)]
  rfl

theorem map_scalar_ySeries (N r ell : ℕ) :
    PowerSeries.map (specialize N r ell) (UniversalTransfer.scalarSeries UniversalTransfer.ySeries) =
      ((TailSeries.scalarE r).reflect r : PowerSeries (A r)) := by
  rw [← map_ySeries N r ell]
  ext i
  simp only [PowerSeries.coeff_map, UniversalTransfer.scalarSeries, specialize_scalar]

/-- The free Euler expression specializes to the actual polynomial Euler expression. -/
theorem map_sSeries_cSeries (N r ell : ℕ) :
    PowerSeries.map (specialize N r ell) (UniversalTransfer.sSeries N r UniversalTransfer.cSeries) =
      ((TailSeries.polynomialOperator N r (TailSeries.cPolynomial N r ell)).reflect
        (r + N * r) : PowerSeries (A r)) := by
  rw [UniversalTransfer.sSeries, CoefficientSeries.map_expression,
    map_scalar_ySeries, map_cSeries,
    reflected_polynomialOperator N r (N * r) _ (TailSeries.cPolynomial_natDegree_le N r ell)]
  rfl

private theorem reflect_nsmul' {B : Type*} [Semiring B] (p : Polynomial B) (b n : ℕ) :
    (n • p).reflect b = n • p.reflect b := by
  ext i
  simp [Polynomial.coeff_reflect]

private theorem coe_nsmul' {B : Type*} [Semiring B] (p : Polynomial B) (n : ℕ) :
    (n • p : Polynomial B) = n • (p : PowerSeries B) :=
  Polynomial.coeToPowerSeries.ringHom.map_nsmul n p

private theorem coe_sub' {B : Type*} [Ring B] (p q : Polynomial B) :
    (p - q : Polynomial B) = (p : PowerSeries B) - (q : PowerSeries B) := by
  ext i
  simp only [Polynomial.coeff_coe, map_sub, Polynomial.coeff_sub]

/-- ET-13 for P: the specialization is the literal actual polynomial reflected
at the common upper exponent (N+1)r, with its shift fully accounted for. -/
theorem map_pSeries (N m r ell : ℕ) (hbound : N * r = ell + m) :
    PowerSeries.map (specialize N r ell) (UniversalTransfer.pSeries N m r) =
      ((TailSeries.pPolynomial N r ell).reflect ((N + 1) * r) : PowerSeries (A r)) := by
  have hell : ell ≤ N * r := by omega
  have htop : (N + 1) * r = r + N * r := by ring
  have hQ : (N + 1) * r = (ell + r) + m := by rw [htop, hbound]; omega
  rw [UniversalTransfer.pSeries, map_sub, map_nsmul, map_mul, map_pow,
    PowerSeries.map_X, map_qSeries, map_sSeries_cSeries,
    TailSeries.pPolynomial_eq N r ell hell, Nat.cast_smul_eq_nsmul, Polynomial.reflect_sub,
    reflect_nsmul', coe_sub', coe_nsmul', htop]
  congr 1
  rw [← htop, hQ, reflect_add_eq_X_pow_mul _ _ _ (TailSeries.qPolynomial_natDegree_le N r ell)]

/-- The coefficient-level specialization has an explicit zero guard beyond its upper exponent. -/
theorem specialize_pSeries_coeff (N m r ell i : ℕ) (hbound : N * r = ell + m) :
    specialize N r ell ((UniversalTransfer.pSeries N m r).coeff i) =
      if i ≤ (N + 1) * r then
        (TailSeries.pPolynomial N r ell).coeff ((N + 1) * r - i) else 0 := by
  have h := congrArg (fun F : PowerSeries (A r) => F.coeff i) (map_pSeries N m r ell hbound)
  rw [PowerSeries.coeff_map, Polynomial.coeff_coe,
    coeff_reflect_of_degree_le _ _ (by
      simpa only [Nat.add_mul, Nat.one_mul] using
        TailSeries.pPolynomial_natDegree_le N r ell (by omega))] at h
  exact h

/-- Every specialized free P coefficient is a finite combination of the designated tail cycles. -/
theorem specialize_pSeries_coeff_mem_finiteTailSpan (N m r ell i : ℕ)
    (hN : 0 < N) (hm : 0 < m) (hbound : N * r = ell + m) :
    specialize N r ell ((UniversalTransfer.pSeries N m r).coeff i) ∈ finiteTailSpan N r ell := by
  rw [specialize_pSeries_coeff N m r ell i hbound]
  split_ifs
  · exact TailSeries.pPolynomial_coeff_mem_finiteTailSpan N r ell _ hN (by omega)
  · exact (finiteTailSpan N r ell).zero_mem

end TorusLinkHomology.UniversalTransferSpecialization
