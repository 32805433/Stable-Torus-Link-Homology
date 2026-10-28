import TorusLinkHomology.Generation.UniversalTransferIdentity
import TorusLinkHomology.Generation.UniversalTransferEvaluation
import TorusLinkHomology.Generation.UniversalTransferDeletion

/-!
# The universal coefficient transfer from the finite exterior identity

The transfer theorem takes the finite universal series identity and its
exterior-degree support as explicit inputs. It proves all differential, no-v,
coefficient-selection, and Q=0 comparisons before specialization.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.UniversalTransfer

@[simp] theorem noVSeries_sSeries_cSeries (N r : ℕ) : NoVSeries (sSeries N r cSeries) :=
  noVSeries_scalar_ySeries.expression noVSeries_cSeries N r (N * r)

theorem noVSeries_jetExpression_sSeries (N r : ℕ)
    (c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1)) :
    NoVSeries (UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
      ySeries (sSeries N r cSeries)) := by
  apply UniversalJets.jetExpression_mem_coeffSubalgebra noVSubalgebra N c _ _ ySeries
    (sSeries N r cSeries)
  · intro s
    exact UniversalJets.evenJetMap_mem_coeffSubalgebra noVSubalgebra (N + 1) (r : ℤ)
      ySeries noVSeries_scalar_ySeries (c s)
  · exact noVSeries_sSeries_cSeries N r

@[simp] theorem eraseQ_jetExpression_sSeries (N r : ℕ)
    (c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1)) :
    PowerSeries.map eraseQ.toRingHom
      (UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
        ySeries (sSeries N r cSeries)) =
      UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
        ySeries (sSeries N r cSeries) := by
  rw [UniversalJets.map_jetExpression (RingHom.id R) eraseQ.toRingHom
    (fun a => eraseQ.commutes a), PowerSeries.map_id, eraseQ_sSeries_cSeries]
  rfl

@[simp] theorem eraseQ_jetExpression_sSeries_coeff (N r : ℕ)
    (c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1)) (i : ℕ) :
    eraseQ ((UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
      ySeries (sSeries N r cSeries)).coeff i) =
      (UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
        ySeries (sSeries N r cSeries)).coeff i := by
  have h := congrArg (fun F : PowerSeries A => F.coeff i)
    (eraseQ_jetExpression_sSeries N r c)
  rw [PowerSeries.coeff_map] at h
  exact h

/-- ET-12 as an equality of free chains. The finite universal exterior
identity is the explicit input `hUniversal`; all comparison hypotheses
needed for no-v uniqueness are discharged by the preceding constructions. -/
theorem transfer_identity_of_universal_series
    (N m r ell q k : ℕ) (hN : 0 < N) (hm : 0 < m) (hbound : N * r = ell + m)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q + 1 = T.card)
    (hkN : k ≤ N) (hkm : k ≤ m)
    (c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1))
    (hc : ∀ s, s.card ≠ q + 1 → c s = 0)
    (hUniversal :
      CoefficientSelector.eulerDeletionSeries (q + 1)
        (CoefficientSelector.selector ((N * r : ℕ) : ℤ) k T)
        ((N * r : ℕ) : ℤ) ((N * r : ℕ) : ℤ) (scalarSeries (ySeries ^ N)) cSeries =
      UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
        ySeries (sSeries N r cSeries)) :
    CoefficientSelector.transferScalar m k T •
      omega N m q (T.orderEmbOfFin hq.symm) =
      d N m ((selectorBoundarySeries (q + 1)
        (CoefficientSelector.selector ((N * r : ℕ) : ℤ) k T)
        ((N * r : ℕ) : ℤ) cSeries).coeff (m + ∑ t ∈ T, t)) +
      ((-1 : ℚ) ^ (q + 1)) •
        ((UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
          ySeries (pSeries N m r)).coeff (m + ∑ t ∈ T, t)) := by
  classical
  have htN (i : Fin (q + 1)) : T.orderEmbOfFin hq.symm i < N :=
    (Finset.mem_range.mp (hT (T.orderEmbOfFin_mem hq.symm i))).trans_le hkN
  have htm (i : Fin (q + 1)) : T.orderEmbOfFin hq.symm i < m :=
    (Finset.mem_range.mp (hT (T.orderEmbOfFin_mem hq.symm i))).trans_le hkm
  apply transfer_identity_of_comparison N m q hN hm _ htN htm
    (CoefficientSelector.transferScalar m k T)
    ((UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
      ySeries (pSeries N m r)).coeff (m + ∑ t ∈ T, t))
    ((UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
      ySeries (sSeries N r cSeries)).coeff (m + ∑ t ∈ T, t))
  · rw [d_selectorBoundarySeries_coeff, selector_deletion_coeff _ m k T hT hq, hUniversal]
    congr 1
    rw [← IsScalarTower.algebraMap_smul R (CoefficientSelector.transferScalar m k T),
      smul_smul, mul_comm]
  · exact jetExpression_pSeries_coeff_is_cycle N m r ell hN hbound c _
  · exact noVSeries_jetExpression_pSeries N m r c _
  · exact noVSeries_jetExpression_sSeries N r c _
  · have h := eraseQ_jetExpression_pSeries_coeff N m r (q + 1) c hc (m + ∑ t ∈ T, t)
    rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, Int.cast_neg, Int.cast_one] at h
    exact h
  · exact eraseQ_jetExpression_sSeries_coeff N r c _

end TorusLinkHomology.UniversalTransfer
