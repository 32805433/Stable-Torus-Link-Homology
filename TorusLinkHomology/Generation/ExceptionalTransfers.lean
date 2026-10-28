import TorusLinkHomology.Generation.JetSeriesSpecialization
import TorusLinkHomology.Generation.UniversalTransferResidue
import TorusLinkHomology.Generation.UniversalTransferConclusion

/-! # Exceptional products transfer into the tail algebra

The finite universal exterior identity is specialized to free coefficient
series, identified with the connecting cycle by no-v uniqueness, and only
then specialized to the actual coefficient complex.
-/

noncomputable section

namespace TorusLinkHomology.UniversalTransfer

/-- The finite universal identity evaluated in the free series, with all
upper exponent bounds in the convention used by the transfer calculation. -/
theorem exists_universal_series_identity (N r q : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree + q ≤ N) :
    ∃ c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1),
      (∀ s, s.card ≠ q → c s = 0) ∧
      CoefficientSelector.eulerDeletionSeries q p ((N * r : ℕ) : ℤ)
        ((N * r : ℕ) : ℤ) (scalarSeries (ySeries ^ N)) cSeries =
      UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
        ySeries (sSeries N r cSeries) := by
  obtain ⟨c, _, hc, hidentity⟩ :=
    UniversalJets.exists_specialized_universal_identity (S := R) (M := V) N q p hp
  refine ⟨c, (fun s hs => hc s (Or.inr hs)), ?_⟩
  have h := hidentity (r : ℤ) ((N * r : ℕ) : ℤ) ySeries
    (fun i => Finsupp.single (Sum.inl i) 1)
  have hbound : (r : ℤ) + ((N * r : ℕ) : ℤ) = (((N + 1) * r : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hbound, ← Nat.cast_mul] at h
  exact h

end TorusLinkHomology.UniversalTransfer

namespace TorusLinkHomology.CoefficientComplex

open UniversalTransferSpecialization

/-- Every nonempty squarefree exceptional product has a connecting class
represented by a polynomial in the designated tail cycles. -/
theorem exceptionalTransfers (N r ell : ℕ) (hN : 0 < N)
    (hm : ell + 1 < N * (r + 1)) : ExceptionalTransfers N r ell := by
  apply exceptionalTransfers_of_specialized_omega N r ell hm
  intro q s hs
  let p := CoefficientSelector.selector ((N * (r + 1) : ℕ) : ℤ)
    (exceptionalCount N r ell) (deficitSet s)
  have hp : p.natDegree + (q + 1) ≤ N :=
    exceptional_selector_degree_bound N r ell q _ s hs
  obtain ⟨c, hc, hidentity⟩ :=
    UniversalTransfer.exists_universal_series_identity N (r + 1) (q + 1) p hp
  apply exceptional_omega_mem_of_deficit_identity N r ell q hN hm s hs c
  exact UniversalTransfer.transfer_identity_of_universal_series
    N (N * (r + 1) - (ell + 1)) (r + 1) (ell + 1) q (exceptionalCount N r ell)
    hN (by omega) (by omega) (deficitSet s) (deficitSet_subset_range s)
    ((card_deficitSet s).trans hs).symm (Nat.min_le_left _ _) (Nat.min_le_right _ _)
    c hc hidentity

end TorusLinkHomology.CoefficientComplex
