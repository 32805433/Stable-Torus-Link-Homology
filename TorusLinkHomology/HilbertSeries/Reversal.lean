import TorusLinkHomology.Generation.Reversal
import TorusLinkHomology.HilbertSeries.AuxiliaryGrading

/-! The active original complex inside the general reversed auxiliary complex.
At offset Nr−m, its m active equations are the equations of K_m, and the
remaining r−m exterior generators have zero differential. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries.GeneralReversal

/-- Include the first m polynomial variables in r variables. -/
def includeCoefficients (m r : ℕ) (hmr : m ≤ r) : R m →+* R r :=
  (MvPolynomial.rename (Fin.castLE hmr)).toRingHom

@[simp] theorem includeCoefficients_u (m r : ℕ) (hmr : m ≤ r) (i : Fin m) :
    includeCoefficients m r hmr (u m i) = u r (Fin.castLE hmr i) := by
  simp [includeCoefficients, u]

private theorem uPolynomial_coeff (n : ℕ) (i : Fin n) :
    (uPolynomial n).coeff i.val = u n i := by
  classical
  simp only [uPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    exact if_neg (fun he => hji (Fin.ext he))
  · simp

private theorem coeff_pow_congr_below {S : Type*} [Semiring S]
    (p q : Polynomial S) (b N : ℕ) (h : ∀ j < b, p.coeff j = q.coeff j)
    (i : ℕ) (hi : i < b) : (p ^ N).coeff i = (q ^ N).coeff i := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ, pow_succ, Polynomial.coeff_mul, Polynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro jk hjk
    have he := Finset.mem_antidiagonal.mp hjk
    rw [ih _ (by omega), h _ (by omega)]

/-- Low coefficient equations are independent of the unused variables. -/
theorem include_differentialCoefficient (N m r : ℕ) (hmr : m ≤ r) (i : Fin m) :
    includeCoefficients m r hmr (differentialCoefficient N m i) =
      differentialCoefficient N r (Fin.castLE hmr i) := by
  have he := coeff_pow_congr_below
    ((uPolynomial m).map (includeCoefficients m r hmr)) (uPolynomial r) m N
    (by
      intro j hj
      rw [Polynomial.coeff_map, uPolynomial_coeff m ⟨j, hj⟩,
        uPolynomial_coeff r ⟨j, lt_of_lt_of_le hj hmr⟩]
      exact includeCoefficients_u m r hmr ⟨j, hj⟩) i.val i.isLt
  simpa only [← Polynomial.map_pow, Polynomial.coeff_map, differentialCoefficient, Fin.val_castLE] using he

/-- Reversed inclusion u_i ↦ e_(r−i). -/
def activeCoefficients (m r : ℕ) (hmr : m ≤ r) : R m →+* R r :=
  (TorusLinkHomology.Reversal.reverseCoefficients r).toRingHom.comp
    (includeCoefficients m r hmr)

@[simp] theorem activeCoefficients_u (m r : ℕ) (hmr : m ≤ r) (i : Fin m) :
    activeCoefficients m r hmr (u m i) =
      CoefficientComplex.e r (Fin.castLE hmr i).rev := by
  simp [activeCoefficients]

/-- Every active coefficient equation is the corresponding reflected equation. -/
theorem active_differentialCoefficient (N m r : ℕ) (hN : 0 < N) (hmr : m ≤ r)
    (i : Fin m) :
    activeCoefficients m r hmr (differentialCoefficient N m i) =
      CoefficientComplex.G N r (N * r - i.val) := by
  change TorusLinkHomology.Reversal.reverseCoefficients r
    (includeCoefficients m r hmr (differentialCoefficient N m i)) = _
  rw [include_differentialCoefficient]
  exact TorusLinkHomology.Reversal.reverse_differentialCoefficient N r hN (Fin.castLE hmr i)

/-- Reverse the first m exterior coordinates; the remaining coordinates are free. -/
def activeVector (m r : ℕ) (hmr : m ≤ r) : V m →ₛₗ[activeCoefficients m r hmr] V r :=
  (Finsupp.linearCombination (R r)
    (fun i : Fin m => Finsupp.single (Fin.castLE hmr i.rev) (1 : R r))).comp
      (Finsupp.mapRange.linearMap (activeCoefficients m r hmr).toSemilinearMap)

@[simp] theorem activeVector_single (m r : ℕ) (hmr : m ≤ r) (i : Fin m) (c : R m) :
    activeVector m r hmr (Finsupp.single i c) =
      Finsupp.single (Fin.castLE hmr i.rev) (activeCoefficients m r hmr c) := by
  simp [activeVector, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Finsupp.linearCombination_single]

/-- The active original algebra in the general auxiliary reversal. -/
def activeChains (m r : ℕ) (hmr : m ≤ r) : A m →+* A r :=
  ExteriorAlgebra.mapOfSemilinear (activeCoefficients m r hmr) (activeVector m r hmr)

@[simp] theorem activeChains_algebraMap (m r : ℕ) (hmr : m ≤ r) (c : R m) :
    activeChains m r hmr (algebraMap (R m) (A m) c) =
      algebraMap (R r) (A r) (activeCoefficients m r hmr c) :=
  ExteriorAlgebra.mapOfSemilinear_algebraMap _ _ _

@[simp] theorem activeChains_xi (m r : ℕ) (hmr : m ≤ r) (i : Fin m) :
    activeChains m r hmr (xi m i) = xi r (Fin.castLE hmr i.rev) := by
  simp [activeChains, xi, ExteriorAlgebra.mapOfSemilinear_iota]

theorem activeChains_smul (m r : ℕ) (hmr : m ≤ r) (c : R m) (x : A m) :
    activeChains m r hmr (c • x) = activeCoefficients m r hmr c • activeChains m r hmr x :=
  ExteriorAlgebra.mapOfSemilinear_smul _ _ _ _

/-- Weight of the active odd generator after coefficient reversal. -/
theorem active_exterior_weight (N m r : ℕ) (hN : 0 < N) (hmr : m ≤ r) (i : Fin m) :
    N * r - m + (Fin.castLE hmr i.rev).val + 1 = N * r - i.val := by
  have hmNr : m ≤ N * r := hmr.trans (by simpa using Nat.mul_le_mul_right r hN)
  simp only [Fin.val_castLE, Fin.val_rev]
  omega

/-- The original K_m differential is the active part of K_(r,Nr−m). -/
theorem activeChains_d (N m r : ℕ) (hN : 0 < N) (hmr : m ≤ r) (x : A m) :
    CoefficientComplex.d N r (N * r - m) (activeChains m r hmr x) =
      activeChains m r hmr (d N m x) := by
  apply ExteriorAlgebra.contractLeft_mapOfSemilinear
  intro a
  induction a using Finsupp.induction with
  | zero => simp
  | single_add i c a hi hc ih =>
    simp only [map_add, activeVector_single, CoefficientComplex.differentialFunctional,
      differentialFunctional, Finsupp.linearCombination_single, smul_eq_mul,
      active_exterior_weight N m r hN hmr, map_mul, active_differentialCoefficient N m r hN hmr] at ih ⊢
    rw [ih]

/-- All exterior generators outside the active block have zero differential. -/
theorem passive_d_xi (N m r : ℕ) (hN : 0 < N) (hmr : m ≤ r) (i : Fin r)
    (hi : m ≤ i.val) : CoefficientComplex.d N r (N * r - m) (xi r i) = 0 := by
  have hmNr : m ≤ N * r := hmr.trans (by simpa using Nat.mul_le_mul_right r hN)
  have hdeg : N * r < N * r - m + i.val + 1 := by omega
  change CoefficientComplex.d N r (N * r - m) (CoefficientComplex.xi r i) = 0
  rw [CoefficientComplex.d_xi, CoefficientComplex.G_eq_zero _ _ _ hdeg, map_zero]

/-- The polynomial and exterior weights of each active original generator. -/
theorem active_polynomial_weight (m r : ℕ) (hmr : m ≤ r) (i : Fin m) :
    (Fin.castLE hmr i).rev.val + 1 = r - i.val := by
  simp only [Fin.val_rev, Fin.val_castLE]
  have := i.isLt
  omega

theorem activeChains_u_mem (N m r : ℕ) (hmr : m ≤ r) (i : Fin m) :
    activeChains m r hmr (algebraMap (R m) (A m) (u m i)) ∈
      Auxiliary.chainPiece (N * r - m) r (r - i.val) 0 := by
  rw [activeChains_algebraMap, activeCoefficients_u, ← active_polynomial_weight m r hmr i]
  exact Auxiliary.e_mem_chainPiece _ _ _

theorem activeChains_xi_mem (N m r : ℕ) (hN : 0 < N) (hmr : m ≤ r) (i : Fin m) :
    activeChains m r hmr (xi m i) ∈ Auxiliary.chainPiece (N * r - m) r (N * r - i.val) 1 := by
  rw [activeChains_xi, ← active_exterior_weight N m r hN hmr i]
  exact Auxiliary.xi_mem_chainPiece _ _ _

/-- Retraction of coefficients, killing the passive polynomial variables. -/
def retractCoefficients (m r : ℕ) : R r →+* R m :=
  (MvPolynomial.aeval (fun i : Fin r => if hi : i.rev.val < m then u m ⟨i.rev.val, hi⟩ else 0)).toRingHom

@[simp] theorem retract_activeCoefficients_u (m r : ℕ) (hmr : m ≤ r) (i : Fin m) :
    retractCoefficients m r (activeCoefficients m r hmr (u m i)) = u m i := by
  rw [activeCoefficients_u]
  change (MvPolynomial.aeval (fun j : Fin r => if hj : j.rev.val < m then u m ⟨j.rev.val, hj⟩ else 0))
    (MvPolynomial.X (Fin.castLE hmr i).rev) = _
  rw [MvPolynomial.aeval_X]
  simp only [Fin.rev_rev, Fin.val_castLE, dif_pos i.isLt]

@[simp] theorem retract_activeCoefficients (m r : ℕ) (hmr : m ≤ r) (c : R m) :
    retractCoefficients m r (activeCoefficients m r hmr c) = c := by
  induction c using MvPolynomial.induction_on with
  | C q =>
    simp [activeCoefficients, includeCoefficients, TorusLinkHomology.Reversal.reverseCoefficients,
      MvPolynomial.renameEquiv, retractCoefficients]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    change retractCoefficients m r (activeCoefficients m r hmr (p * u m i)) = p * u m i
    rw [map_mul, map_mul, hp, retract_activeCoefficients_u]

/-- Retraction of exterior coordinates, killing the passive exterior variables. -/
def retractVector (m r : ℕ) : V r →ₛₗ[retractCoefficients m r] V m :=
  (Finsupp.linearCombination (R m)
    (fun i : Fin r => if hi : i.val < m then Finsupp.single (⟨i.val, hi⟩ : Fin m).rev (1 : R m) else 0)).comp
      (Finsupp.mapRange.linearMap (retractCoefficients m r).toSemilinearMap)

/-- An algebraic retraction of the active original complex. -/
def retractChains (m r : ℕ) : A r →+* A m :=
  ExteriorAlgebra.mapOfSemilinear (retractCoefficients m r) (retractVector m r)

theorem retractChains_smul (m r : ℕ) (c : R r) (x : A r) :
    retractChains m r (c • x) = retractCoefficients m r c • retractChains m r x :=
  ExteriorAlgebra.mapOfSemilinear_smul _ _ _ _

@[simp] theorem retractChains_active_xi (m r : ℕ) (hmr : m ≤ r) (i : Fin m) :
    retractChains m r (xi r (Fin.castLE hmr i.rev)) = xi m i := by
  simp only [retractChains, xi, ExteriorAlgebra.mapOfSemilinear_iota, retractVector,
    LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    RingHom.toSemilinearMap_apply, Finsupp.linearCombination_single, Fin.val_castLE, dif_pos i.rev.isLt]
  congr 1
  change retractCoefficients m r 1 • Finsupp.single i.rev.rev (1 : R m) = Finsupp.single i 1
  rw [map_one, one_smul, Fin.rev_rev]

@[simp] theorem retract_activeChains (m r : ℕ) (hmr : m ≤ r) (x : A m) :
    retractChains m r (activeChains m r hmr x) = x := by
  induction x using CoordinateKoszul.induction_on_generators m with
  | hone => simp
  | hadd a b ha hb => simp [ha, hb]
  | hsmul c a ha => rw [activeChains_smul, retractChains_smul, retract_activeCoefficients, ha]
  | hxi i a ha => rw [map_mul, map_mul, activeChains_xi, retractChains_active_xi, ha]

/-- The active K_m chain algebra embeds in the auxiliary chain algebra. -/
theorem activeChains_injective (m r : ℕ) (hmr : m ≤ r) : Function.Injective (activeChains m r hmr) :=
  Function.LeftInverse.injective (retract_activeChains m r hmr)

end TorusLinkHomology.HilbertSeries.GeneralReversal
