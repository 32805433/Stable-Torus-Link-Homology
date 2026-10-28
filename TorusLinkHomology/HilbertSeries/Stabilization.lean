import TorusLinkHomology.HilbertSeries.GradedHomology
import Mathlib.Data.Finset.Preimage
import DGA.ExteriorScalarChange

/-! Stabilization of homogeneous chain spaces by extension of indices. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries
open CoordinateKoszul

/-- The usual inclusion of polynomial rings by extension of variable indices. -/
def extendCoefficients (n : ℕ) : R n →+* R (n + 1) :=
  (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom

@[simp] theorem extendCoefficients_u (n : ℕ) (i : Fin n) :
    extendCoefficients n (u n i) = u (n + 1) i.castSucc := by
  simp [extendCoefficients, u]

/-- Add the final term to the truncated coefficient polynomial. -/
theorem uPolynomial_succ (n : ℕ) :
    uPolynomial (n + 1) = (uPolynomial n).map (extendCoefficients n) +
      Polynomial.monomial n (u (n + 1) (Fin.last n)) := by
  simp [uPolynomial, Fin.sum_univ_castSucc, Polynomial.map_sum]

private theorem coeff_pow_congr_below {S : Type*} [Semiring S]
    (p q : Polynomial S) (b N : ℕ)
    (h : ∀ j < b, p.coeff j = q.coeff j) (i : ℕ) (hi : i < b) :
    (p ^ N).coeff i = (q ^ N).coeff i := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    rw [pow_succ, pow_succ, Polynomial.coeff_mul, Polynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro jk hjk
    have hsum := Finset.mem_antidiagonal.mp hjk
    rw [ih _ (by omega), h _ (by omega)]

/-- The old coefficient equations are unchanged by adjoining a new variable. -/
theorem extend_differentialCoefficient (N n : ℕ) (i : Fin n) :
    extendCoefficients n (differentialCoefficient N n i) =
      differentialCoefficient N (n + 1) i.castSucc := by
  have he := coeff_pow_congr_below (uPolynomial (n + 1))
    ((uPolynomial n).map (extendCoefficients n)) n N (by
      intro j hj
      rw [uPolynomial_succ]
      simp [Polynomial.coeff_monomial, Nat.ne_of_gt hj]) i.val i.isLt
  simpa [differentialCoefficient, ← Polynomial.map_pow] using he.symm

/-- Extend the exterior generator indices and the polynomial coefficients. -/
def extendVector (n : ℕ) : V n →ₛₗ[extendCoefficients n] V (n + 1) :=
  (Finsupp.linearCombination (R (n + 1))
    (fun i : Fin n => Finsupp.single i.castSucc (1 : R (n + 1)))).comp
      (Finsupp.mapRange.linearMap (extendCoefficients n).toSemilinearMap)

@[simp] theorem extendVector_single (n : ℕ) (i : Fin n) (r : R n) :
    extendVector n (Finsupp.single i r) =
      Finsupp.single i.castSucc (extendCoefficients n r) := by
  change Finsupp.linearCombination (R (n + 1))
    (fun i : Fin n => Finsupp.single i.castSucc (1 : R (n + 1)))
    (Finsupp.mapRange (extendCoefficients n) (map_zero _) (Finsupp.single i r)) = _
  rw [Finsupp.mapRange_single, Finsupp.linearCombination_single]
  simp

/-- Inclusion of the original coefficient Koszul algebras. -/
def extendChains (n : ℕ) : A n →+* A (n + 1) :=
  ExteriorAlgebra.mapOfSemilinear (extendCoefficients n) (extendVector n)

@[simp] theorem extendChains_iota (n : ℕ) (v : V n) :
    extendChains n (ExteriorAlgebra.ι (R n) v) =
      ExteriorAlgebra.ι (R (n + 1)) (extendVector n v) :=
  ExteriorAlgebra.mapOfSemilinear_iota _ _ _

@[simp] theorem extendChains_algebraMap (n : ℕ) (r : R n) :
    extendChains n (algebraMap (R n) (A n) r) =
      algebraMap (R (n + 1)) (A (n + 1)) (extendCoefficients n r) :=
  ExteriorAlgebra.mapOfSemilinear_algebraMap _ _ _

theorem extendChains_smul (n : ℕ) (r : R n) (x : A n) :
    extendChains n (r • x) = extendCoefficients n r • extendChains n x :=
  ExteriorAlgebra.mapOfSemilinear_smul _ _ _ _

@[simp] theorem extendChains_xi (n : ℕ) (i : Fin n) :
    extendChains n (xi n i) = xi (n + 1) i.castSucc := by
  simp [xi]

/-- The algebra inclusion commutes with the Koszul differential for every N. -/
theorem extendChains_d (N n : ℕ) (x : A n) :
    d N (n + 1) (extendChains n x) = extendChains n (d N n x) := by
  apply ExteriorAlgebra.contractLeft_mapOfSemilinear
  intro v
  induction v using Finsupp.induction with
  | zero => simp
  | single_add i r v _ _ ih =>
    simp only [map_add, extendVector_single, differentialFunctional,
      Finsupp.linearCombination_single, smul_eq_mul, map_mul,
      extend_differentialCoefficient] at ih ⊢
    rw [ih]

/-- Set the final polynomial variable to zero. -/
def retractCoefficients (n : ℕ) : R (n + 1) →+* R n :=
  (MvPolynomial.aeval (Fin.lastCases 0 (u n))).toRingHom

@[simp] theorem retractCoefficients_u_castSucc (n : ℕ) (i : Fin n) :
    retractCoefficients n (u (n + 1) i.castSucc) = u n i := by
  simp [retractCoefficients, u]

@[simp] theorem retract_extendCoefficients (n : ℕ) (r : R n) :
    retractCoefficients n (extendCoefficients n r) = r := by
  induction r using MvPolynomial.induction_on with
  | C q => simp [extendCoefficients, retractCoefficients]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [extendCoefficients, retractCoefficients, u]

/-- Set the final exterior generator to zero as well. -/
def retractVector (n : ℕ) : V (n + 1) →ₛₗ[retractCoefficients n] V n :=
  (Finsupp.linearCombination (R n)
    (Fin.lastCases 0 (fun i : Fin n => Finsupp.single i (1 : R n)))).comp
      (Finsupp.mapRange.linearMap (retractCoefficients n).toSemilinearMap)

@[simp] theorem retractVector_single_castSucc (n : ℕ) (i : Fin n) (r : R (n + 1)) :
    retractVector n (Finsupp.single i.castSucc r) =
      Finsupp.single i (retractCoefficients n r) := by
  simp [retractVector, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Finsupp.linearCombination_single]

/-- An algebraic left inverse of the chain inclusion. It need not commute with d. -/
def retractChains (n : ℕ) : A (n + 1) →+* A n :=
  ExteriorAlgebra.mapOfSemilinear (retractCoefficients n) (retractVector n)

@[simp] theorem retractChains_xi_castSucc (n : ℕ) (i : Fin n) :
    retractChains n (xi (n + 1) i.castSucc) = xi n i := by
  simp [retractChains, xi, ExteriorAlgebra.mapOfSemilinear_iota]

theorem retractChains_smul (n : ℕ) (r : R (n + 1)) (x : A (n + 1)) :
    retractChains n (r • x) = retractCoefficients n r • retractChains n x :=
  ExteriorAlgebra.mapOfSemilinear_smul _ _ _ _

@[simp] theorem retract_extendChains (n : ℕ) (x : A n) :
    retractChains n (extendChains n x) = x := by
  induction x using induction_on_generators n with
  | hone => simp
  | hadd x y hx hy => simp [hx, hy]
  | hsmul r x hx => rw [extendChains_smul, retractChains_smul, retract_extendCoefficients, hx]
  | hxi i x hx => simp [hx]

theorem extendChains_injective (n : ℕ) : Function.Injective (extendChains n) :=
  Function.LeftInverse.injective (retract_extendChains n)

/-- Add one unused polynomial and exterior generator to a monomial. -/
def extendBoundedMonomial (n a : ℕ) (m : BoundedMonomial n a) : BoundedMonomial (n + 1) a :=
  (Fin.lastCases 0 m.1, m.2.map (Fin.castSuccEmb (n := n)))

@[simp] theorem hasDegree_extendBoundedMonomial (N n a b h : ℕ)
    (m : BoundedMonomial n a) :
    HasDegree N (n + 1) a b h (extendBoundedMonomial n a m) ↔ HasDegree N n a b h m := by
  simp [HasDegree, extendBoundedMonomial, Fin.sum_univ_castSucc, Finset.sum_map]

theorem extendBoundedMonomial_injective (n a : ℕ) :
    Function.Injective (extendBoundedMonomial n a) := by
  intro m m' he
  apply Prod.ext
  · funext i
    simpa [extendBoundedMonomial] using congrArg (fun x : BoundedMonomial (n + 1) a => x.1 i.castSucc) he
  · exact Finset.map_injective (Fin.castSuccEmb (n := n)) (congrArg Prod.snd he)

/-- A monomial of weight below n does not use the newly added index n. -/
theorem HasDegree.last_unused {N n a b h : ℕ} {m : BoundedMonomial (n + 1) a}
    (hm : HasDegree N (n + 1) a b h m) (hb : b < n) :
    m.1 (Fin.last n) = 0 ∧ Fin.last n ∉ m.2 := by
  constructor
  · apply Fin.ext
    by_contra he
    have hi := hm.polynomial_index_le he
    simp only [Fin.val_last] at hi
    omega
  · intro he
    have hi := hm.exterior_index_le he
    simp only [Fin.val_last] at hi
    omega

/-- Restriction to the old indices, used when the new index is absent. -/
def restrictBoundedMonomial (n a : ℕ) (m : BoundedMonomial (n + 1) a) : BoundedMonomial n a :=
  (fun i => m.1 i.castSucc,
    m.2.preimage (Fin.castSuccEmb (n := n)) (Fin.castSuccEmb (n := n)).injective.injOn)

@[simp] theorem restrict_extendBoundedMonomial (n a : ℕ) (m : BoundedMonomial n a) :
    restrictBoundedMonomial n a (extendBoundedMonomial n a m) = m := by
  apply Prod.ext
  · funext i; simp [restrictBoundedMonomial, extendBoundedMonomial]
  · exact Finset.preimage_map (Fin.castSuccEmb (n := n)) m.2

theorem extend_restrictBoundedMonomial (n a : ℕ) (m : BoundedMonomial (n + 1) a)
    (hp : m.1 (Fin.last n) = 0) (he : Fin.last n ∉ m.2) :
    extendBoundedMonomial n a (restrictBoundedMonomial n a m) = m := by
  apply Prod.ext
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [extendBoundedMonomial, restrictBoundedMonomial] using hp.symm
    · simp [extendBoundedMonomial, restrictBoundedMonomial]
  · ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [extendBoundedMonomial, restrictBoundedMonomial, he]
    · simp [extendBoundedMonomial, restrictBoundedMonomial]

/-- Extension and restriction are inverse on the homogeneous monomial indices
as soon as the number of old generators is greater than the weight. -/
def homogeneousMonomialEquivSucc (N n a b h : ℕ) (hb : b < n) :
    {m : BoundedMonomial n a // HasDegree N n a b h m} ≃
      {m : BoundedMonomial (n + 1) a // HasDegree N (n + 1) a b h m} where
  toFun m := ⟨extendBoundedMonomial n a m.val,
    (hasDegree_extendBoundedMonomial N n a b h m.val).mpr m.property⟩
  invFun m := ⟨restrictBoundedMonomial n a m.val, by
    apply (hasDegree_extendBoundedMonomial N n a b h _).mp
    rw [extend_restrictBoundedMonomial n a m.val (m.property.last_unused hb).1
      (m.property.last_unused hb).2]
    exact m.property⟩
  left_inv m := Subtype.ext (restrict_extendBoundedMonomial n a m.val)
  right_inv m := Subtype.ext (extend_restrictBoundedMonomial n a m.val
    (m.property.last_unused hb).1 (m.property.last_unused hb).2)

/-- The homogeneous rational basis, with exactly the original bounded indices. -/
def homogeneousChainBasis (N n a b h : ℕ) :
    Module.Basis {m : BoundedMonomial n a // HasDegree N n a b h m}
      ℚ (chainPiece N n a b h) :=
  Module.Basis.span ((chainMonomial_linearIndependent n a).comp
    Subtype.val Subtype.val_injective)

/-- A concrete linear equivalence sending each monomial to its extension. -/
def chainPieceEquivSucc (N n a b h : ℕ) (hb : b < n) :
    chainPiece N n a b h ≃ₗ[ℚ] chainPiece N (n + 1) a b h :=
  (homogeneousChainBasis N n a b h).equiv (homogeneousChainBasis N (n + 1) a b h)
    (homogeneousMonomialEquivSucc N n a b h hb)

@[simp] theorem chainPieceEquivSucc_basis (N n a b h : ℕ) (hb : b < n)
    (m : {m : BoundedMonomial n a // HasDegree N n a b h m}) :
    chainPieceEquivSucc N n a b h hb (homogeneousChainBasis N n a b h m) =
      homogeneousChainBasis N (n + 1) a b h (homogeneousMonomialEquivSucc N n a b h hb m) :=
  Module.Basis.equiv_apply _ _ _ _

theorem finrank_chainPiece_succ_stable (N n a b h : ℕ) (hb : b < n) :
    Module.finrank ℚ (chainPiece N n a b h) =
      Module.finrank ℚ (chainPiece N (n + 1) a b h) :=
  (chainPieceEquivSucc N n a b h hb).finrank_eq

/-- All lengths greater than the weight have the same homogeneous chain dimension. -/
theorem finrank_chainPiece_stable (N n a b h : ℕ) (hb : b < n) :
    Module.finrank ℚ (chainPiece N n a b h) =
      Module.finrank ℚ (chainPiece N (b + 1) a b h) := by
  induction n, Nat.succ_le_of_lt hb using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [← finrank_chainPiece_succ_stable N n a b h (by omega)]
    exact ih (by omega)

end TorusLinkHomology.HilbertSeries
