import TorusLinkHomology.Generation.ContinuationSeries
import TorusLinkHomology.Generation.ContinuationBaseChange
import TorusLinkHomology.Generation.TailSeries
import TorusLinkHomology.Generation.Comparison

/-!
# Continuing the tail recurrence below the offset

Write `n = r + 1`, and let `U` be the reversal of `E`. Over a field in which the
last coefficient is invertible, the tail recurrence at offset `ell` continues to
every lower exponent. In deficit coordinates from `Nn`, this continuation `Y`
solves `U DY - N (DU) Y = P`, where `P` is the closed polynomial built from the
tails above `Nn`. It extends the old tails up to deficit `Nn - ell - 1`, and its
differential is `U ^ N` in every deficit.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientComplex

open CoefficientSeries

namespace Continuation

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

theorem scalarE_natDegree_le (r : ℕ) : (TailSeries.scalarE r).natDegree ≤ r :=
  Polynomial.natDegree_map_le.trans (E_natDegree_le r)

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

/-- The reversal of `E`, as a series in deficits from its top degree. -/
def revE (r : ℕ) : PowerSeries (R r) := ((E r).reflect r : Polynomial (R r))

theorem coeff_revE (r i : ℕ) : (revE r).coeff i = reversedCoeff r (E r) i := by
  rw [revE, Polynomial.coeff_coe, coeff_reflect_of_degree_le r (E r) (E_natDegree_le r)]

/-- The top coefficient of `E` is the last variable. -/
theorem coeff_revE_zero (r : ℕ) : (revE (r + 1)).coeff 0 = e (r + 1) (Fin.last r) := by
  classical
  rw [coeff_revE, reversedCoeff, if_pos (Nat.zero_le _), Nat.sub_zero, E]
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Polynomial.coeff_one, Nat.succ_ne_zero, if_false, zero_add]
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp
  · intro i _ hi
    rw [if_neg]
    intro h
    exact hi (Fin.ext (by simpa using h))
  · simp

/-- Powers of the reversal are the reversed coefficients of `E ^ N`. -/
theorem coeff_revE_pow (N r i : ℕ) :
    ((revE r) ^ N).coeff i = if i ≤ N * r then G N r (N * r - i) else 0 := by
  have h : (revE r) ^ N = (((E r) ^ N).reflect (N * r) : Polynomial (R r)) := by
    rw [reflect_pow_of_degree_le (E r) r N (E_natDegree_le r), revE, Polynomial.coe_pow]
  rw [h, Polynomial.coeff_coe, coeff_reflect_of_degree_le (N * r) _
    (Polynomial.natDegree_pow_le_of_le N (E_natDegree_le r))]
  rfl

/-- The chain algebra version of the reversal of `E`. -/
theorem map_revE (r : ℕ) :
    PowerSeries.map (algebraMap (R r) (A r)) (revE r) =
      ((TailSeries.scalarE r).reflect r : Polynomial (A r)) := by
  ext i
  rw [PowerSeries.coeff_map, coeff_revE, Polynomial.coeff_coe,
    coeff_reflect_of_degree_le r _ (scalarE_natDegree_le r)]
  simp only [reversedCoeff, TailSeries.scalarE]
  split_ifs
  · simp
  · simp

/-- The tail at deficit `j` from `Nr`. Past the constant term this is zero. -/
def tailDeficit (N r ell j : ℕ) : V r := tailVector N r ell (N * r - j)

theorem iota_tailDeficit (N r ell j : ℕ) :
    ExteriorAlgebra.ι (R r) (tailDeficit N r ell j) = tail N r ell (N * r - j) :=
  iota_tailVector N r ell _

/-- The negative of `cPolynomial` has the tails as its reversed coefficients. -/
theorem iotaSeries_tailDeficit (N r ell : ℕ) :
    ExteriorAlgebra.iotaSeries (R := R r) (tailDeficit N r ell) =
      ((-TailSeries.cPolynomial N r ell).reflect (N * r) : Polynomial (A r)) := by
  have hdeg : (-TailSeries.cPolynomial N r ell).natDegree ≤ N * r := by
    rw [Polynomial.natDegree_neg]
    exact TailSeries.cPolynomial_natDegree_le N r ell
  ext j
  rw [ExteriorAlgebra.coeff_iotaSeries, iota_tailDeficit, Polynomial.coeff_coe,
    coeff_reflect_of_degree_le _ _ hdeg, reversedCoeff]
  split_ifs with hj
  · rw [Polynomial.coeff_neg, TailSeries.coeff_cPolynomial, TailSeries.C,
      if_pos (Nat.sub_le _ _), neg_neg]
    rfl
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hj)]
    exact tail_eq_zero N r ell 0 (Nat.zero_le _)

/-- The degree-one vector underlying a coefficient of `P`. -/
def pVector (N r ell j : ℕ) : V r := ExteriorAlgebra.ιInv (TailSeries.P N r ell j)

@[simp] theorem iota_pVector (N r ell j : ℕ) :
    ExteriorAlgebra.ι (R r) (pVector N r ell j) = TailSeries.P N r ell j := by
  have h := TailSeries.P_mem_degree_one N r ell j
  change TailSeries.P N r ell j ∈ LinearMap.range (ExteriorAlgebra.ι (R r)) ^ 1 at h
  rw [pow_one] at h
  obtain ⟨v, hv⟩ := h
  unfold pVector
  rw [← hv, ExteriorAlgebra.ι_leftInverse]

/-- Every coefficient of `P` is closed, which on vectors says the functional vanishes. -/
theorem differentialFunctional_pVector (N r ell j : ℕ) (hN : 0 < N) (hell : ell ≤ N * r) :
    differentialFunctional N r ell (pVector N r ell j) = 0 := by
  apply (ExteriorAlgebra.algebraMap_inj (M := V r) _ _).mp
  have h := TailSeries.d_P N r ell j hN hell
  rw [← iota_pVector N r ell j] at h
  change CliffordAlgebra.contractLeft (Q := 0) (differentialFunctional N r ell)
    (ExteriorAlgebra.ι (R r) (pVector N r ell j)) = _ at h
  simpa only [CliffordAlgebra.contractLeft_ι, map_zero] using h

/-- Up to the old offset, the tails satisfy the Euler equation with forcing `P`. -/
theorem eulerDeficit_tailDeficit (N r ell h : ℕ) (hh : h < N * r - ell) :
    eulerDeficit N (revE r) (tailDeficit N r ell) h = pVector N r ell (N * r + r - h) := by
  apply ExteriorAlgebra.ι_inj (R r) _ _ |>.mp
  rw [iota_pVector]
  rw [← coeff_expression_iotaSeries N (r : ℤ) ((N * r : ℕ) : ℤ) (by push_cast; rfl),
    map_revE, iotaSeries_tailDeficit]
  have hdeg : (-TailSeries.cPolynomial N r ell).natDegree ≤ N * r := by
    rw [Polynomial.natDegree_neg]
    exact TailSeries.cPolynomial_natDegree_le N r ell
  have hexpr := reflected_polynomialOperator N r (N * r) _ hdeg
  have hcoe : CoefficientSeries.expression N (r : ℤ) ((N * r : ℕ) : ℤ)
      (((TailSeries.scalarE r).reflect r : Polynomial (A r)) : PowerSeries (A r))
      (((-TailSeries.cPolynomial N r ell).reflect (N * r) : Polynomial (A r)) : PowerSeries (A r)) =
      ((TailSeries.polynomialOperator N r (-TailSeries.cPolynomial N r ell)).reflect
        (r + N * r) : Polynomial (A r)) := hexpr.symm
  rw [hcoe, Polynomial.coeff_coe,
    coeff_reflect_of_degree_le _ _ (polynomialOperator_natDegree_le N r (N * r) _ hdeg),
    reversedCoeff, if_pos (by omega), TailSeries.coeff_polynomialOperator]
  have hneg : (-TailSeries.cPolynomial N r ell).coeff = -TailSeries.C N r ell := by
    funext j
    simp [TailSeries.coeff_cPolynomial]
  have hJ : r + N * r - h = N * r + r - h := by rw [add_comm]
  rw [hneg, map_neg, hJ, TailSeries.P, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
    TailSeries.Q_support N r ell _ (by omega), smul_zero, zero_sub]

/-- Comparison with the next offset fixes every coefficient of `P`. -/
theorem J_P (N r ell j : ℕ) (hN : 0 < N) (hm : ell + 1 < N * r) :
    J N r (ell + 1) (TailSeries.P N r (ell + 1) j) = TailSeries.P N r ell j := by
  rw [TailSeries.P_eq_eulerOperator_W _ _ _ hN, TailSeries.P_eq_eulerOperator_W _ _ _ hN]
  change (J N r (ell + 1)).toLinearMap _ = _
  rw [TailSeries.map_eulerOperator]
  have hW : (fun k => (J N r (ell + 1)).toLinearMap (TailSeries.W N r (ell + 1) k)) =
      TailSeries.W N r ell := by
    funext k
    simp only [TailSeries.W, TailSeries.X]
    split_ifs with hk
    · have h := J_tail N r (ell + 1) k (by omega)
      simp only [Nat.add_sub_cancel] at h
      change J N r (ell + 1) (-tail N r (ell + 1) k) = _
      rw [map_neg, h]
    · change J N r (ell + 1) 0 = 0
      exact map_zero _
  rw [hW]

variable (N r ell : ℕ) (F : Type*) [Field F] [Algebra (R (r + 1)) F]

/-- The reversal of `E` over the larger field. -/
def revF : PowerSeries F := PowerSeries.map (algebraMap (R (r + 1)) F) (revE (r + 1))

/-- The forcing term `P` over the larger field, in deficits from `N(r+1)+(r+1)`. -/
def forcingF (h : ℕ) : VF (r + 1) F :=
  vecF (r + 1) F (pVector N (r + 1) ell (N * (r + 1) + (r + 1) - h))

/-- The continuation of the tails, in deficits from `N(r+1)`. -/
def contY : ℕ → VF (r + 1) F :=
  eulerSolution N (revF r F) (forcingF N r ell F) (vecF (r + 1) F (tailDeficit N (r + 1) ell 0))

variable {F}

theorem revF_coeff_zero_ne_zero [IsFractionRing (R (r + 1)) F] : (revF r F).coeff 0 ≠ 0 := by
  rw [revF, PowerSeries.coeff_map, coeff_revE_zero]
  intro h
  exact MvPolynomial.X_ne_zero (Fin.last r)
    ((IsFractionRing.injective (R (r + 1)) F) (h.trans (map_zero _).symm))

variable {N r ell}

/-- Up to deficit `N(r+1)-ell-1`, the continuation is the old tail. -/
theorem contY_eq_tail [IsFractionRing (R (r + 1)) F] [CharZero F] (h : ℕ)
    (hh : h < N * (r + 1) - ell) :
    contY N r ell F h = vecF (r + 1) F (tailDeficit N (r + 1) ell h) := by
  apply eq_of_eulerDeficit_eq N (revF r F) (revF_coeff_zero_ne_zero r) _ _
    (N * (r + 1) - ell - 1) (by simp [contY]) _ h (by omega)
  intro j hj hjK
  rw [contY, eulerDeficit_eulerSolution N _ (revF_coeff_zero_ne_zero r) _ _ j hj, forcingF,
    ← eulerDeficit_tailDeficit N (r + 1) ell j (by omega), map_eulerDeficit]
  rfl

/-- The continuation satisfies the Euler equation at every deficit. -/
theorem eulerDeficit_contY [IsFractionRing (R (r + 1)) F] [CharZero F]
    (hm : ell < N * (r + 1)) (h : ℕ) :
    eulerDeficit N (revF r F) (contY N r ell F) h = forcingF N r ell F h := by
  by_cases hh : h = 0
  · subst h
    have hP := eulerDeficit_tailDeficit N (r + 1) ell 0 (by omega)
    rw [eulerDeficit_zero] at hP
    rw [eulerDeficit_zero, forcingF, ← hP, map_zero]
  · exact eulerDeficit_eulerSolution N _ (revF_coeff_zero_ne_zero r) _ _ h hh

/-- The differential of the continuation is `U ^ N` at every deficit. -/
theorem functionalF_contY [IsFractionRing (R (r + 1)) F] [CharZero F]
    (hN : 0 < N) (hm : ell < N * (r + 1)) (h : ℕ) :
    functionalF F N (r + 1) ell (contY N r ell F h) = ((revF r F) ^ N).coeff h := by
  apply eq_of_eulerDeficit_eq N (revF r F) (revF_coeff_zero_ne_zero r)
    (fun k => functionalF F N (r + 1) ell (contY N r ell F k))
    (fun k => ((revF r F) ^ N).coeff k) h _ _ h le_rfl
  · simp only [contY, eulerSolution_zero, functionalF_vecF, revF, ← map_pow, PowerSeries.coeff_map,
      coeff_revE_pow, Nat.zero_le, if_true, Nat.sub_zero, tailDeficit]
    rw [differentialFunctional_tailVector N (r + 1) ell _ hm]
  · intro j _ _
    have hL := map_eulerDeficit (RingHom.id F) (functionalF F N (r + 1) ell) N
      (revF r F) (contY N r ell F) j
    rw [PowerSeries.map_id] at hL
    have hR := coeff_expression_scalar N ((r + 1 : ℕ) : ℤ) ((N : ℤ) * ((r + 1 : ℕ) : ℤ)) rfl
      (revF r F) ((revF r F) ^ N) j
    rw [expression_pow] at hR
    simp only [map_zero] at hR
    rw [← hR]
    exact hL.symm.trans (by
      rw [eulerDeficit_contY hm, forcingF]
      erw [functionalF_vecF]
      rw [differentialFunctional_pVector N (r + 1) ell _ hN hm.le, map_zero])

end Continuation

end TorusLinkHomology.CoefficientComplex
