import TorusLinkHomology.Generation.ComparisonExactness

/-!
# The projection formula for the comparison

The formula holds for arbitrary chains. After reducing coefficients, the
distinguished contraction of the right J-factor is zero, so no homogeneity
assumption or choice of a Koszul sign is needed.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientComplex

/-- Dropping the first old generator reduces every tail above the new offset
to the corresponding tail in the smaller-rank complex. -/
theorem dropFirst_tail (N r ell j : ℕ) (hj : ell + 1 < j) :
    dropFirst r (tail N (r + 1) ell j) = tail N r (ell + 1) j := by
  classical
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases htop : j ≤ ell + (r + 1)
    · let i : Fin r := ⟨j - ell - 2, by omega⟩
      have hold : j = ell + i.succ.val + 1 := by dsimp [i]; omega
      have hnew : j = (ell + 1) + i.val + 1 := by dsimp [i]; omega
      rw [hold, tail_initial, dropFirst_xi_succ, ← tail_initial N r (ell + 1) i]
      congr 1
      omega
    · have hgt : ell + (r + 1) < j := Nat.lt_of_not_ge htop
      rw [tail_eq_of_gt _ _ _ _ hgt, dropFirst_smul, reduce_invNat,
        tail_eq_of_gt N r (ell + 1) j (by omega), map_sum]
      simp only [dropFirst_smul]
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

/-- Reduction of J on the common exterior algebra agrees with rho. -/
theorem dropFirst_J (N r ell : ℕ) (b : A (r + 1)) :
    dropFirst r (J N (r + 1) (ell + 1) b) = rhoSucc N r (ell + 1) b := by
  have hvector (v : V (r + 1)) :
      dropFirst r (J N (r + 1) (ell + 1) (ExteriorAlgebra.ι (R (r + 1)) v)) =
        rhoSucc N r (ell + 1) (ExteriorAlgebra.ι (R (r + 1)) v) := by
    induction v using Finsupp.induction with
    | zero => simp only [map_zero]
    | @single_add i c v _ _ hv =>
      simp only [map_add, hv]
      congr 1
      have hi : ExteriorAlgebra.ι (R (r + 1)) (Finsupp.single i c) =
          c • xi (r + 1) i := by simp [xi, ← map_smul, Finsupp.smul_single]
      rw [hi, map_smul, dropFirst_smul, rhoSucc_smul, J_xi, rhoSucc_xi]
      congr 1
      simpa only [Nat.add_sub_cancel_right] using
        dropFirst_tail N r ell (ell + 1 + i.val + 1) (by omega)
  induction b using CliffordAlgebra.left_induction with
  | algebraMap c => rw [AlgHom.commutes, dropFirst_algebraMap, rhoSucc_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx => simp only [map_mul, hvector, hx]

/-- Multiplication by a right factor with zero projected contraction obeys
the ordinary product rule after coefficient reduction. -/
theorem p_mul_of_right_zero (r : ℕ) (x y : A (r + 1)) (hy : p r y = 0) :
    p r (x * y) = p r x * dropFirst r y := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c =>
    change dropFirst r (CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r)
      (algebraMap (R (r + 1)) (A (r + 1)) c * y)) = _
    rw [CliffordAlgebra.contractLeft_algebraMap_mul, map_mul, dropFirst_algebraMap]
    change algebraMap (R r) (A r) (reduceCoefficients r c) * p r y = _
    rw [hy, mul_zero]
    simp [p]
  | add x z hx hz =>
    simp only [add_mul, p_add, hx, hz]
  | ι_mul x v hx =>
    have hp (z : A (r + 1)) :
        p r (ExteriorAlgebra.ι (R (r + 1)) v * z) =
          reduceCoefficients r (firstCoordinate r v) • dropFirst r z -
            dropFirst r (ExteriorAlgebra.ι (R (r + 1)) v) * p r z := by
      rw [p, CliffordAlgebra.contractLeft_ι_mul, map_sub, dropFirst_smul, map_mul]
      rfl
    rw [mul_assoc, hp, hp, hx, map_mul, sub_mul, smul_mul_assoc, mul_assoc]

/-- The chain-level projection formula used by the connecting construction. -/
theorem p_mul_J (N r ell : ℕ) (w b : A (r + 1)) :
    p r (w * J N (r + 1) (ell + 1) b) = p r w * rhoSucc N r (ell + 1) b := by
  rw [p_mul_of_right_zero r w _ (p_J N r ell b), dropFirst_J]

end TorusLinkHomology.CoefficientComplex
