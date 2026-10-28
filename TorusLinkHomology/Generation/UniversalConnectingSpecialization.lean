import TorusLinkHomology.Generation.UniversalConnecting
import TorusLinkHomology.Generation.UniversalTransferSpecialization
import TorusLinkHomology.Generation.ExceptionalGeneration

/-!
# The universal connecting cycle specializes to the actual connecting class

The free odd generators specialize to negative tail generators. An ordered
product of length q therefore represents (-1)^q times the positive exceptional
product. This sign is retained before giving the positive normalization.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.UniversalTransferSpecialization

open CoefficientComplex

/-- The leading coefficient of the actual polynomial is the final coefficient variable. -/
theorem evenMap_y_zero (N r ell : ℕ) :
    evenMap N (r + 1) (ell + 1) (UniversalTransfer.y 0) = e (r + 1) (Fin.last r) := by
  rw [evenMap_y, reversedCoeff, if_pos (Nat.zero_le _), Nat.sub_zero]
  classical
  simp only [E, Polynomial.coeff_add, Polynomial.coeff_one, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, zero_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp
  · intro j _ hj
    exact if_neg (fun h => hj (Fin.ext (by simp only [Fin.val_last]; omega)))
  · simp

@[simp] theorem evenMap_v_zero (N r ell : ℕ) :
    evenMap N (r + 1) (ell + 1) (UniversalTransfer.v 0) = G N (r + 1) (ell + 1) := by
  rw [evenMap_v, if_pos (Nat.zero_le _), Nat.sub_zero]

/-- Every exceptional odd generator is the negative actual high tail. -/
theorem specialize_oddA_exceptional (N r ell t : ℕ)
    (ht : t < N * (r + 1) - (ell + 1)) :
    specialize N (r + 1) (ell + 1) (UniversalTransfer.oddA t) =
      -tail N (r + 1) (ell + 1) (N * (r + 1) - t) := by
  rw [specialize_oddA, oddAImage, reversedCoeff, if_pos (by omega),
    TailSeries.coeff_cPolynomial, TailSeries.C, if_pos (Nat.sub_le _ _)]
  rfl

/-- The rational free normalization remains the literal rational normalization. -/
theorem evenMap_etaCoefficient (N r ell : ℕ) :
    evenMap N (r + 1) (ell + 1)
        (UniversalTransfer.etaCoefficient N (N * (r + 1) - (ell + 1))) =
      -((N : R (r + 1)) * invNat (r + 1) (N * (r + 1) - (ell + 1))) := by
  simp [UniversalTransfer.etaCoefficient, evenMap, invNat, neg_mul]

/-- The free distinguished odd generator specializes to the explicit comparison generator. -/
theorem specialize_etaPrime (N r ell : ℕ) (hm : ell + 1 < N * (r + 1)) :
    specialize N (r + 1) (ell + 1)
        (UniversalTransfer.etaPrime N (N * (r + 1) - (ell + 1))) =
      CoefficientComplex.etaPrime N r ell := by
  rw [UniversalTransfer.etaPrime, specialize_smul, evenMap_etaCoefficient,
    specialize_oddQ, oddQImage, reversedCoeff, if_pos (Nat.zero_le _), Nat.sub_zero,
    TailSeries.etaPrime_eq_qPolynomial_coeff N r ell hm]
  congr 2
  omega

/-- The mapped universal omega is exactly the comparison expression. -/
theorem specialize_omega (N r ell q : ℕ) (hm : ell + 1 < N * (r + 1))
    (t : Fin (q + 1) → ℕ) :
    specialize N (r + 1) (ell + 1)
        (UniversalTransfer.omega N (N * (r + 1) - (ell + 1)) q t) =
      connectingOmega N r ell
        (specialize N (r + 1) (ell + 1) (UniversalTransfer.orderedA (q + 1) t))
        (specialize N (r + 1) (ell + 1) (UniversalTransfer.betaDeletion N q t)) := by
  rw [UniversalTransfer.omega, map_add, specialize_smul, evenMap_v_zero,
    map_mul, specialize_etaPrime N r ell hm]
  rfl

/-- The actual beta deletion is supplied by the exact quotient constructed in the free ring. -/
theorem d_specialize_orderedA (N r ell q : ℕ) (hm : ell + 1 < N * (r + 1))
    (t : Fin (q + 1) → ℕ) (htN : ∀ i, t i < N)
    (htm : ∀ i, t i < N * (r + 1) - (ell + 1)) :
    d N (r + 1) (ell + 1)
        (specialize N (r + 1) (ell + 1) (UniversalTransfer.orderedA (q + 1) t)) =
      -e (r + 1) (Fin.last r) •
        specialize N (r + 1) (ell + 1) (UniversalTransfer.betaDeletion N q t) := by
  rw [d_specialize N (r + 1) (ell + 1) (Nat.le_of_lt hm),
    UniversalTransfer.d_orderedA N _ q t htN htm, specialize_smul, map_neg,
    evenMap_y_zero]

/-- Before the sign normalization, specialization already provides the exact connecting lift. -/
theorem specialize_omega_represents (N r ell q : ℕ) (hm : ell + 1 < N * (r + 1))
    (t : Fin (q + 1) → ℕ) (htN : ∀ i, t i < N)
    (htm : ∀ i, t i < N * (r + 1) - (ell + 1)) :
    ConnectingRepresentative N r ell
      (rhoSucc N r (ell + 1)
        (specialize N (r + 1) (ell + 1) (UniversalTransfer.orderedA (q + 1) t)))
      (specialize N (r + 1) (ell + 1)
        (UniversalTransfer.omega N (N * (r + 1) - (ell + 1)) q t)) := by
  rw [specialize_omega N r ell q hm]
  exact connectingOmega_represents N r ell hm _ _
    (d_specialize_orderedA N r ell q hm t htN htm)

/-- Reduction retains each negative exceptional tail, including its sign. -/
theorem rho_specialize_oddA (N r ell t : ℕ)
    (ht : t < N * (r + 1) - (ell + 1)) :
    rhoSucc N r (ell + 1)
        (specialize N (r + 1) (ell + 1) (UniversalTransfer.oddA t)) =
      -tail N r (ell + 1) (N * (r + 1) - t) := by
  rw [specialize_oddA_exceptional N r ell t ht, map_neg,
    rhoSucc_tail N r (ell + 1) _ (by omega)]

/-- The sign of the reduced ordered product is exactly its number of odd factors. -/
theorem rho_specialize_orderedA (N r ell q : ℕ) (t : Fin q → ℕ)
    (ht : ∀ i, t i < N * (r + 1) - (ell + 1)) :
    rhoSucc N r (ell + 1)
        (specialize N (r + 1) (ell + 1) (UniversalTransfer.orderedA q t)) =
      (-1 : R r) ^ q • ExteriorAlgebra.ιMulti (R r) q
        (fun i => tailVector N r (ell + 1) (N * (r + 1) - t i)) := by
  have hi (i : Fin q) :
      rhoSucc N r (ell + 1) (specialize N (r + 1) (ell + 1)
          (ExteriorAlgebra.ι UniversalTransfer.R (Finsupp.single (Sum.inl (t i)) 1))) =
        ExteriorAlgebra.ι (R r) (-tailVector N r (ell + 1) (N * (r + 1) - t i)) := by
    rw [map_neg, iota_tailVector]
    exact rho_specialize_oddA N r ell (t i) (ht i)
  calc
    _ = ExteriorAlgebra.ιMulti (R r) q
        (fun i => -tailVector N r (ell + 1) (N * (r + 1) - t i)) := by
      simp only [UniversalTransfer.orderedA, ExteriorAlgebra.ιMulti_apply,
        map_list_prod, List.map_ofFn]
      congr 1
      exact congrArg List.ofFn (funext hi)
    _ = _ := by
      simpa only [neg_smul, one_smul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (ExteriorAlgebra.ιMulti (R r) q).map_smul_univ (fun _ => (-1 : R r))
          (fun i => tailVector N r (ell + 1) (N * (r + 1) - t i))

private theorem exceptionalProduct_eq_iotaMulti_of_card (N r ell q : ℕ)
    (s : Finset (Fin (exceptionalCount N r ell))) (hq : s.card = q) :
    exceptionalProduct N r ell s = ExteriorAlgebra.ιMulti (R r) q
      (fun i => tailVector N r (ell + 1) (N * (r + 1) - (s.orderEmbOfFin hq i).val)) := by
  subst q
  exact exceptionalProduct_eq_iotaMulti N r ell s

/-- ET-14 with the unnormalized sign: the free omega represents the signed
canonical exceptional product. -/
theorem specialize_omega_represents_exceptional (N r ell q : ℕ)
    (hm : ell + 1 < N * (r + 1))
    (s : Finset (Fin (exceptionalCount N r ell))) (hs : s.card = q + 1) :
    ConnectingRepresentative N r ell
      ((-1 : R r) ^ (q + 1) • exceptionalProduct N r ell s)
      (specialize N (r + 1) (ell + 1)
        (UniversalTransfer.omega N (N * (r + 1) - (ell + 1)) q
          (fun i => (s.orderEmbOfFin hs i).val))) := by
  have htN (i : Fin (q + 1)) : (s.orderEmbOfFin hs i).val < N :=
    (s.orderEmbOfFin hs i).isLt.trans_le (Nat.min_le_left _ _)
  have htm (i : Fin (q + 1)) :
      (s.orderEmbOfFin hs i).val < N * (r + 1) - (ell + 1) :=
    (s.orderEmbOfFin hs i).isLt.trans_le (Nat.min_le_right _ _)
  have h := specialize_omega_represents N r ell q hm
    (fun i => (s.orderEmbOfFin hs i).val) htN htm
  rw [rho_specialize_orderedA N r ell (q + 1) _ htm,
    ← exceptionalProduct_eq_iotaMulti_of_card N r ell (q + 1) s hs] at h
  exact h

/-- The explicit normalization for the positive exceptional product. -/
def normalizedExceptionalOmega (N r ell q : ℕ)
    (s : Finset (Fin (exceptionalCount N r ell))) (hs : s.card = q + 1) : A (r + 1) :=
  (-1 : R (r + 1)) ^ (q + 1) •
    specialize N (r + 1) (ell + 1)
      (UniversalTransfer.omega N (N * (r + 1) - (ell + 1)) q
        (fun i => (s.orderEmbOfFin hs i).val))

/-- Multiplying the specialized omega by the same sign gives the positive
exceptional product, with no sign convention left implicit. -/
theorem normalizedExceptionalOmega_represents (N r ell q : ℕ)
    (hm : ell + 1 < N * (r + 1))
    (s : Finset (Fin (exceptionalCount N r ell))) (hs : s.card = q + 1) :
    ConnectingRepresentative N r ell (exceptionalProduct N r ell s)
      (normalizedExceptionalOmega N r ell q s hs) := by
  have h := (specialize_omega_represents_exceptional N r ell q hm s hs).smul
    ((-1 : R (r + 1)) ^ (q + 1))
  simpa only [map_pow, map_neg, map_one, smul_smul, ← mul_pow, neg_mul_neg,
    one_mul, one_pow, one_smul, normalizedExceptionalOmega] using h

/-- A tail-plus-boundary identity for each literal specialization finishes
the exceptional transfer statement, including the positive-product sign. -/
theorem exceptionalTransfers_of_specialized_omega (N r ell : ℕ)
    (hm : ell + 1 < N * (r + 1))
    (hgood : ∀ (q : ℕ) (s : Finset (Fin (exceptionalCount N r ell)))
      (hs : s.card = q + 1),
      specialize N (r + 1) (ell + 1)
        (UniversalTransfer.omega N (N * (r + 1) - (ell + 1)) q
          (fun i => (s.orderEmbOfFin hs i).val)) ∈
        tailRepresentativeSpace N (r + 1) (ell + 1)) :
    ExceptionalTransfers N r ell := by
  apply exceptionalTransfers_of_representatives N r ell hm
  intro s hs
  have hcard : 1 ≤ s.card := hs.card_pos
  have heq : s.card = (s.card - 1) + 1 := (Nat.sub_add_cancel hcard).symm
  refine ⟨normalizedExceptionalOmega N r ell (s.card - 1) s heq,
    normalizedExceptionalOmega_represents N r ell (s.card - 1) hm s heq, ?_⟩
  exact (tailRepresentativeSpace N (r + 1) (ell + 1)).smul_mem _ (hgood _ s heq)

end TorusLinkHomology.UniversalTransferSpecialization
