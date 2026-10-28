import TorusLinkHomology.Basic
import TorusLinkHomology.Generation.CoefficientComplex
import DGA.ExteriorScalarChange

/-!
# Reversing the original coefficient Koszul complex

Reversal of both polynomial variables and odd generators identifies the
original differential with the auxiliary differential at offset `(N - 1) * n`.
The polynomial argument uses reflection at a fixed upper degree, so it also
works without a separate leading-coefficient calculation.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.Reversal

open Polynomial

private theorem coeff_pow_congr_below {S : Type*} [Semiring S]
    (p q : Polynomial S) (b N : ℕ)
    (h : ∀ j < b, p.coeff j = q.coeff j) (i : ℕ) (hi : i < b) :
    (p ^ N).coeff i = (q ^ N).coeff i := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro jk hjk
    have hsum := Finset.mem_antidiagonal.mp hjk
    rw [ih _ (by omega), h _ (by omega)]

private theorem reflect_pow_of_degree_le {S : Type*} [Semiring S]
    (p : Polynomial S) (b N : ℕ) (hp : p.natDegree ≤ b) :
    (p ^ N).reflect (N * b) = (p.reflect b) ^ N := by
  induction N with
  | zero => simp [Polynomial.reflect_one]
  | succ N ih =>
    rw [pow_succ, Nat.succ_mul,
      Polynomial.reflect_mul _ _ (Polynomial.natDegree_pow_le_of_le N hp) hp, ih, pow_succ]

/-- Permute `u_i` to the auxiliary variable `e_{n-i}`. -/
def reverseCoefficients (n : ℕ) : R n ≃ₐ[ℚ] R n :=
  MvPolynomial.renameEquiv ℚ Fin.revPerm

@[simp] theorem reverseCoefficients_u (n : ℕ) (i : Fin n) :
    reverseCoefficients n (u n i) = CoefficientComplex.e n i.rev := by
  simp [reverseCoefficients, u, CoefficientComplex.e, MvPolynomial.renameEquiv,
    Fin.revPerm]

@[simp] theorem reverseCoefficients_involutive (n : ℕ) (r : R n) :
    reverseCoefficients n (reverseCoefficients n r) = r := by
  exact (reverseCoefficients n).left_inv r

private theorem uPolynomial_coeff (n : ℕ) (i : Fin n) :
    (uPolynomial n).coeff i.val = u n i := by
  classical
  simp only [uPolynomial, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact if_neg (fun h => hji (Fin.ext h))
  · simp

private theorem uPolynomial_coeff_eq_zero (n j : ℕ) (hj : n ≤ j) :
    (uPolynomial n).coeff j = 0 := by
  classical
  simp only [uPolynomial, finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (by have := i.isLt; omega)

private theorem E_coeff_pos (n : ℕ) (i : Fin n) :
    (CoefficientComplex.E n).coeff (i.val + 1) = CoefficientComplex.e n i := by
  classical
  simp only [CoefficientComplex.E, coeff_add, coeff_one, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, zero_add, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact if_neg (fun h => hji (Fin.ext (by omega)))
  · simp

/-- The reflected auxiliary polynomial is the reversed original polynomial
with its monic degree-`n` term added. -/
theorem reflect_E (n : ℕ) :
    (CoefficientComplex.E n).reflect n =
      (uPolynomial n).map (reverseCoefficients n).toRingHom + X ^ n := by
  classical
  ext j : 1
  rw [coeff_reflect, coeff_add, coeff_map, coeff_X_pow]
  by_cases hj : j < n
  · rw [Polynomial.revAt_le (Nat.le_of_lt hj), if_neg (by omega)]
    have hi : n - j = (Fin.rev (⟨j, hj⟩ : Fin n)).val + 1 := by
      simp only [Fin.val_rev]
      omega
    rw [hi, E_coeff_pos, uPolynomial_coeff n ⟨j, hj⟩, add_zero]
    exact (reverseCoefficients_u n ⟨j, hj⟩).symm
  · rw [uPolynomial_coeff_eq_zero _ _ (Nat.le_of_not_gt hj), map_zero, zero_add]
    by_cases hjn : j = n
    · subst j
      rw [Polynomial.revAt_le le_rfl, Nat.sub_self, CoefficientComplex.E_coeff_zero,
        if_pos rfl]
    · rw [Polynomial.revAt_eq_self_of_lt (by omega), if_neg (by omega)]
      exact coeff_eq_zero_of_natDegree_lt
        ((CoefficientComplex.E_natDegree_le n).trans_lt (by omega))

/-- Reversal identifies each of the equations defining the two complexes. -/
theorem reverse_differentialCoefficient (N n : ℕ) (hN : 0 < N) (i : Fin n) :
    reverseCoefficients n (differentialCoefficient N n i) =
      CoefficientComplex.G N n (N * n - i.val) := by
  have hi : i.val ≤ N * n := by
    have hnN : n ≤ N * n := by simpa using Nat.mul_le_mul_right n hN
    omega
  have hpow := congrArg (fun p : Polynomial (R n) => p.coeff i.val)
    (reflect_pow_of_degree_le (CoefficientComplex.E n) n N
      (CoefficientComplex.E_natDegree_le n))
  rw [coeff_reflect, Polynomial.revAt_le hi, reflect_E] at hpow
  have hlow := coeff_pow_congr_below
    ((uPolynomial n).map (reverseCoefficients n).toRingHom + X ^ n)
    ((uPolynomial n).map (reverseCoefficients n).toRingHom) n N
    (by intro j hj; simp [coeff_X_pow, Nat.ne_of_lt hj])
    i.val i.isLt
  rw [hlow, ← Polynomial.map_pow, coeff_map] at hpow
  exact hpow.symm

/-- Reverse the odd basis and its polynomial coefficients simultaneously. -/
def reverseVector (n : ℕ) : V n →ₛₗ[(reverseCoefficients n).toRingHom] V n :=
  (Finsupp.linearCombination (R n)
    (fun i : Fin n => Finsupp.single i.rev (1 : R n))).comp
      (Finsupp.mapRange.linearMap (reverseCoefficients n).toRingHom.toSemilinearMap)

@[simp] theorem reverseVector_single (n : ℕ) (i : Fin n) (r : R n) :
    reverseVector n (Finsupp.single i r) =
      Finsupp.single i.rev (reverseCoefficients n r) := by
  change Finsupp.linearCombination (R n)
    (fun i : Fin n => Finsupp.single i.rev (1 : R n))
    (Finsupp.mapRange (reverseCoefficients n) (map_zero _) (Finsupp.single i r)) = _
  rw [Finsupp.mapRange_single, Finsupp.linearCombination_single]
  simp

theorem reverseVector_involutive (n : ℕ) (v : V n) :
    reverseVector n (reverseVector n v) = v := by
  induction v using Finsupp.induction with
  | zero => rw [map_zero, map_zero]
  | single_add i r v _ _ ih =>
    simp only [map_add, reverseVector_single, Fin.rev_rev,
      reverseCoefficients_involutive, ih]

/-- The involutive ring map underlying coefficient reversal. -/
def reverseChains (n : ℕ) : A n →+* A n :=
  ExteriorAlgebra.mapOfSemilinear (reverseCoefficients n).toRingHom (reverseVector n)

@[simp] theorem reverseChains_iota (n : ℕ) (v : V n) :
    reverseChains n (ExteriorAlgebra.ι (R n) v) =
      ExteriorAlgebra.ι (R n) (reverseVector n v) :=
  ExteriorAlgebra.mapOfSemilinear_iota _ _ _

@[simp] theorem reverseChains_algebraMap (n : ℕ) (r : R n) :
    reverseChains n (algebraMap (R n) (A n) r) =
      algebraMap (R n) (A n) (reverseCoefficients n r) :=
  ExteriorAlgebra.mapOfSemilinear_algebraMap _ _ _

theorem reverseChains_smul (n : ℕ) (r : R n) (x : A n) :
    reverseChains n (r • x) = reverseCoefficients n r • reverseChains n x :=
  ExteriorAlgebra.mapOfSemilinear_smul _ _ _ _

@[simp] theorem reverseChains_xi (n : ℕ) (i : Fin n) :
    reverseChains n (xi n i) = CoefficientComplex.xi n i.rev := by
  simp only [xi, CoefficientComplex.xi, reverseChains_iota, reverseVector_single, map_one]

theorem reverseChains_involutive (n : ℕ) (x : A n) :
    reverseChains n (reverseChains n x) = x := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι v => simp only [reverseChains_iota, reverseVector_involutive]
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The coefficient reversal is a ring isomorphism, semilinear over the
involutive permutation of polynomial variables. -/
def reverseChainEquiv (n : ℕ) : A n ≃+* A n where
  toFun := reverseChains n
  invFun := reverseChains n
  left_inv := reverseChains_involutive n
  right_inv := reverseChains_involutive n
  map_mul' := map_mul (reverseChains n)
  map_add' := map_add (reverseChains n)

theorem reverse_functional (N n : ℕ) (hN : 0 < N) (v : V n) :
    CoefficientComplex.differentialFunctional N n ((N - 1) * n) (reverseVector n v) =
      reverseCoefficients n (differentialFunctional N n v) := by
  have h :
      (CoefficientComplex.differentialFunctional N n ((N - 1) * n)).comp
        (reverseVector n) =
      (reverseCoefficients n).toRingHom.toSemilinearMap.comp
        (differentialFunctional N n) := by
    apply Finsupp.lhom_ext
    intro i r
    simp only [LinearMap.comp_apply, reverseVector_single]
    have hind : (N - 1) * n + i.rev.val + 1 = N * n - i.val := by
      rw [Nat.sub_mul]
      have hnN : n ≤ N * n := by simpa using Nat.mul_le_mul_right n hN
      have := i.isLt
      simp only [Fin.val_rev]
      omega
    simp only [CoefficientComplex.differentialFunctional, differentialFunctional,
      Finsupp.linearCombination_single, smul_eq_mul, RingHom.toSemilinearMap_apply,
      hind]
    change reverseCoefficients n r * _ =
      reverseCoefficients n (r * differentialCoefficient N n i)
    rw [map_mul, reverse_differentialCoefficient N n hN]
  exact LinearMap.congr_fun h v

/-- The original complex is isomorphic to the auxiliary one at offset
`(N - 1) * n`; in particular, exponent one goes directly to offset zero. -/
theorem reverseChains_d (N n : ℕ) (hN : 0 < N) (x : A n) :
    CoefficientComplex.d N n ((N - 1) * n) (reverseChains n x) =
      reverseChains n (d N n x) :=
  ExteriorAlgebra.contractLeft_mapOfSemilinear _ _ _ _ (reverse_functional N n hN) x

end TorusLinkHomology.Reversal
