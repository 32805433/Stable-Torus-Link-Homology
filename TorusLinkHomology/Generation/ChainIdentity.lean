import TorusLinkHomology.Generation.ContinuationTail
import TorusLinkHomology.Generation.SelectorBoundary
import TorusLinkHomology.Generation.JetSeriesSpecialization
import TorusLinkHomology.Generation.UniversalTransferConclusion
import Mathlib.Algebra.CharP.Algebra

/-!
# The chain identity for exceptional products

The continuation `Y` of the tails has differential `U ^ N` and satisfies
`U DY - N (DU) Y = P`. The universal polynomial identity then computes the
differential of the ordered selector product of `Y` as a polynomial in `P`, with
no denominators. Extracting one coefficient gives the required representative,
and the resulting identity descends from the field to the coefficient ring.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientComplex

namespace Continuation

open CoefficientSeries CoefficientSelector UniversalTransferSpecialization

variable (N r ell : ℕ) (F : Type*) [Field F] [Algebra (R (r + 1)) F]

/-- The comparison map followed by extension of scalars. -/
def comparisonF : A (r + 1) →+* AF (r + 1) F :=
  (toF (r + 1) F).comp (J N (r + 1) (ell + 1)).toRingHom

/-- The coefficients of `P` at the new offset, in deficits from `N(r+1)+(r+1)`. -/
def pSeries : PowerSeries (A (r + 1)) :=
  PowerSeries.mk fun h => TailSeries.P N (r + 1) (ell + 1) (N * (r + 1) + (r + 1) - h)

variable {N r ell F}

theorem comparisonF_apply (x : A (r + 1)) :
    comparisonF N r ell F x = toF (r + 1) F (J N (r + 1) (ell + 1) x) := rfl

theorem comparisonF_algebraMap (c : R (r + 1)) :
    comparisonF N r ell F (algebraMap (R (r + 1)) (A (r + 1)) c) =
      algebraMap F (AF (r + 1) F) (algebraMap (R (r + 1)) F c) := by
  rw [comparisonF_apply, AlgHom.commutes, toF_algebraMap]

theorem comparisonF_smul_rat [Algebra ℚ F] (w : ℚ) (x : A (r + 1)) :
    comparisonF N r ell F (algebraMap ℚ (R (r + 1)) w • x) =
      algebraMap ℚ F w • comparisonF N r ell F x := by
  rw [comparisonF_apply, map_smul, toF_smul, RingHom.map_rat_algebraMap]
  rfl

/-- Below the new offset, the comparison map sends new tails to the continuation. -/
theorem comparisonF_tailDeficit [IsFractionRing (R (r + 1)) F] [CharZero F] (h : ℕ)
    (hh : h < N * (r + 1) - (ell + 1)) :
    comparisonF N r ell F (ExteriorAlgebra.ι (R (r + 1)) (tailDeficit N (r + 1) (ell + 1) h)) =
      ExteriorAlgebra.ι F (contY N r ell F h) := by
  have hJ := J_tail N (r + 1) (ell + 1) (N * (r + 1) - h) (by omega)
  simp only [Nat.add_sub_cancel] at hJ
  rw [comparisonF_apply, iota_tailDeficit, hJ, contY_eq_tail h (by omega), ← iota_tailDeficit,
    toF_iota]

/-- The generator at deficit `N(r+1)-(ell+1)` is the distinguished generator of the old complex. -/
theorem toF_xi_zero [IsFractionRing (R (r + 1)) F] [CharZero F]
    (hm : ell + 1 < N * (r + 1)) :
    toF (r + 1) F (xi (r + 1) 0) =
      ExteriorAlgebra.ι F (contY N r ell F (N * (r + 1) - (ell + 1))) := by
  rw [contY_eq_tail _ (by omega), ← toF_iota, iota_tailDeficit,
    show N * (r + 1) - (N * (r + 1) - (ell + 1)) = ell + (0 : Fin (r + 1)).val + 1 by
      simp only [Fin.val_zero]
      omega,
    tail_initial]

/-- The Euler expression of the continuation is the image of `P` at every deficit. -/
theorem expression_contY [IsFractionRing (R (r + 1)) F] [CharZero F]
    (hN : 0 < N) (hm : ell + 1 < N * (r + 1)) :
    expression N ((r + 1 : ℕ) : ℤ) ((N * (r + 1) : ℕ) : ℤ)
        (PowerSeries.map (algebraMap F (AF (r + 1) F)) (revF r F))
        (ExteriorAlgebra.iotaSeries (R := F) (contY N r ell F)) =
      PowerSeries.map (comparisonF N r ell F) (pSeries N r ell) := by
  ext h
  rw [coeff_expression_iotaSeries N _ _ (by push_cast; rfl), eulerDeficit_contY (by omega),
    PowerSeries.coeff_map, pSeries, PowerSeries.coeff_mk, comparisonF_apply,
    J_P N (r + 1) ell _ hN hm, forcingF, ← toF_iota, iota_pVector]

/-- The polynomial in `P` is a tail chain at the new offset. -/
theorem jetExpression_pSeries_coeff_mem (hN : 0 < N) (hm : ell + 1 < N * (r + 1))
    (c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1)) (u v : ℤ) (i : ℕ) :
    (UniversalJets.jetExpression N c u v (revE (r + 1)) (pSeries N r ell)).coeff i ∈
      tailSubalgebra N (r + 1) (ell + 1) := by
  apply UniversalJets.jetExpression_coeff_mem
  intro j
  rw [pSeries, PowerSeries.coeff_mk]
  exact finiteTailSpan_le_tailSubalgebra N (r + 1) (ell + 1) hm
    (TailSeries.P_mem_finiteTailSpan N (r + 1) (ell + 1) _ hN hm)

variable (F) in
/-- Every exceptional product has a connecting representative that is a tail
chain plus a boundary. -/
theorem exists_exceptional_representative [IsFractionRing (R (r + 1)) F] [Algebra ℚ F]
    [CharZero F] (hN : 0 < N) (hm : ell + 1 < N * (r + 1))
    (s : Finset (Fin (exceptionalCount N r ell))) :
    ∃ z : A (r + 1), ConnectingRepresentative N r ell (exceptionalProduct N r ell s) z ∧
      z ∈ tailRepresentativeSpace N (r + 1) (ell + 1) := by
  classical
  let T := deficitSet s
  have hT : T ⊆ Finset.range (exceptionalCount N r ell) := deficitSet_subset_range s
  have hq : s.card = T.card := (card_deficitSet s).symm
  let m := N * (r + 1) - (ell + 1)
  have hkm : exceptionalCount N r ell ≤ m := Nat.min_le_right _ _
  let b : ℤ := ((N * (r + 1) : ℕ) : ℤ)
  have hb : (N : ℤ) * ((r + 1 : ℕ) : ℤ) = b := by simp [b]
  let sel := selector b (exceptionalCount N r ell) T
  have hsel : sel.natDegree + s.card ≤ N := by
    rw [natDegree_selector_add_card b s]
    exact Nat.min_le_left _ _
  let D := m + ∑ t ∈ T, t
  let C := contY N r ell F
  let f := functionalF F N (r + 1) ell
  obtain ⟨coeff, _, _, hid⟩ :=
    UniversalJets.exists_specialized_universal_identity (S := F) (M := VF (r + 1) F)
      N s.card sel hsel
  -- The differential of the selector product is a polynomial in `P`.
  let Aterm := (UniversalJets.jetExpression N coeff ((r + 1 : ℕ) : ℤ)
    (((r + 1 : ℕ) : ℤ) + b) (revE (r + 1)) (pSeries N r ell)).coeff D
  have hAterm : Aterm ∈ tailSubalgebra N (r + 1) (ell + 1) :=
    jetExpression_pSeries_coeff_mem hN hm coeff _ _ D
  have hdiff : CliffordAlgebra.contractLeft (Q := 0) f
      ((selectorBoundarySeries s.card sel b (ExteriorAlgebra.iotaSeries (R := F) C)).coeff D) =
      comparisonF N r ell F Aterm := by
    have h₁ := hid ((r + 1 : ℕ) : ℤ) b (revF r F) C
    rw [hb] at h₁
    have h₂ := contractSeries_selectorBoundary f s.card sel b C ((revF r F) ^ N)
      (functionalF_contY hN (by omega))
    have h₃ : (PowerSeries.map (algebraMap F (AF (r + 1) F)) (revF r F) *
          shiftedEuler b (ExteriorAlgebra.iotaSeries (R := F) C) -
        N • (shiftedEuler ((r + 1 : ℕ) : ℤ)
          (PowerSeries.map (algebraMap F (AF (r + 1) F)) (revF r F)) *
          ExteriorAlgebra.iotaSeries (R := F) C)) =
        PowerSeries.map (comparisonF N r ell F) (pSeries N r ell) :=
      expression_contY hN hm
    rw [h₃] at h₁
    have h₄ := UniversalJets.map_jetExpression (algebraMap (R (r + 1)) F)
      (comparisonF N r ell F) comparisonF_algebraMap N coeff ((r + 1 : ℕ) : ℤ)
      (((r + 1 : ℕ) : ℤ) + b) (revE (r + 1)) (pSeries N r ell)
    have h₅ := congrArg (fun G => PowerSeries.coeff D G) (h₂.trans (h₁.trans h₄.symm))
    simpa only [coeff_contractSeries, PowerSeries.coeff_map] using h₅
  -- The chains of the coefficient extraction, over the coefficient ring.
  let Cr : ℕ → V (r + 1) := fun h => if h < m then tailDeficit N (r + 1) (ell + 1) h else 0
  let bterm := (selectorBoundarySeries s.card sel b
    (ExteriorAlgebra.iotaSeries (R := R (r + 1)) Cr)).coeff D
  let a := ExteriorAlgebra.ιMulti (R (r + 1)) s.card
    (fun j => tailDeficit N (r + 1) (ell + 1) (T.orderEmbOfFin hq.symm j))
  let w := xi (r + 1) 0 * J N (r + 1) (ell + 1) a
  have hbterm : comparisonF N r ell F bterm =
      (selectorBoundarySeries s.card sel b (ExteriorAlgebra.iotaSeries (R := F)
        (fun h => if h < m then C h else 0))).coeff D := by
    have h := map_selectorBoundarySeries (comparisonF N r ell F) comparisonF_smul_rat Cr
      (fun h => if h < m then C h else 0) (fun h => by
        by_cases hh : h < m
        · simp only [Cr, if_pos hh]
          exact comparisonF_tailDeficit h hh
        · simp [Cr, if_neg hh])
      s.card sel b
    have h' := congrArg (fun G => PowerSeries.coeff D G) h
    simpa only [PowerSeries.coeff_map] using h'
  have hTm (j : Fin s.card) : T.orderEmbOfFin hq.symm j < m :=
    (Finset.mem_range.mp (hT (T.orderEmbOfFin_mem hq.symm j))).trans_le hkm
  have ha : comparisonF N r ell F a = ExteriorAlgebra.ιMulti F s.card
      (fun j => C (T.orderEmbOfFin hq.symm j)) :=
    map_iotaMulti _ _ _ _ (fun j => comparisonF_tailDeficit _ (hTm j))
  -- The coefficient extraction and the differential of its two terms.
  have hsplit := selectorBoundarySeries_coeff_split (R := F) b m (exceptionalCount N r ell) T
    hT hq hkm C
  have hκ : (algebraMap (R (r + 1)) F) (algebraMap ℚ (R (r + 1)) (transferScalar m
      (exceptionalCount N r ell) T)) = algebraMap ℚ F (transferScalar m
      (exceptionalCount N r ell) T) := RingHom.map_rat_algebraMap _ _
  let c := algebraMap ℚ (R (r + 1)) (transferScalar m (exceptionalCount N r ell) T)
  have hchain : toF (r + 1) F (J N (r + 1) (ell + 1) Aterm) =
      toF (r + 1) F (J N (r + 1) (ell + 1) (d N (r + 1) (ell + 1) bterm) +
        c • d N (r + 1) ell w) := by
    have hdJ := d_J N (r + 1) (ell + 1) bterm
    simp only [Nat.add_sub_cancel] at hdJ
    rw [map_add, toF_smul, ← hdJ, toF_d, toF_d, ← comparisonF_apply, ← comparisonF_apply, ← hdiff]
    change CliffordAlgebra.contractLeft (Q := 0) f _ = CliffordAlgebra.contractLeft (Q := 0) f _ +
      _ • CliffordAlgebra.contractLeft (Q := 0) f _
    rw [hsplit, map_add, map_smul, hbterm, ← ha, ← toF_xi_zero hm, comparisonF_apply a, ← map_mul]
    congr 1
    change _ • _ = (algebraMap (R (r + 1)) F) (algebraMap ℚ (R (r + 1)) _) • _
    rw [hκ]
  have hJ := toF_injective hchain
  have hκne : transferScalar m (exceptionalCount N r ell) T ≠ 0 :=
    exceptional_transferScalar_ne_zero N r ell s
  let c' := algebraMap ℚ (R (r + 1)) (transferScalar m (exceptionalCount N r ell) T)⁻¹
  have hcc : c' * c = 1 := by
    change algebraMap ℚ (R (r + 1)) _ * algebraMap ℚ (R (r + 1)) _ = 1
    rw [← map_mul, inv_mul_cancel₀ hκne, map_one]
  refine ⟨c' • (Aterm - d N (r + 1) (ell + 1) bterm), ⟨w, ?_, ?_⟩, ?_⟩
  · change p r (xi (r + 1) 0 * J N (r + 1) (ell + 1) a) = _
    have hxi : p r (xi (r + 1) 0) = 1 := by
      rw [p, xi, CliffordAlgebra.contractLeft_ι, dropFirst_algebraMap]
      simp [firstCoordinate]
    rw [p_mul_J, hxi, one_mul, exceptionalProduct_eq_iotaMulti]
    apply map_iotaMulti
    intro j
    have hj : T.orderEmbOfFin hq.symm j = (s.orderEmbOfFin rfl j).val :=
      (congrFun (orderEmbOfFin_deficitSet s rfl) j).symm
    have hbound := hTm j
    rw [iota_tailDeficit, rhoSucc_tail N r (ell + 1) _ (by omega), iota_tailVector, hj]
  · rw [map_smul, map_sub, hJ, add_sub_cancel_left, smul_smul, hcc, one_smul]
  · refine ⟨c' • Aterm, (tailSubalgebra N (r + 1) (ell + 1)).smul_mem hAterm _,
      -(c' • bterm), ?_⟩
    rw [map_neg, map_smul, smul_sub]
    abel

end Continuation

/-- Exceptional products transfer into the tail algebra, by the continuation of
the tail recurrence over the fraction field. -/
theorem exceptionalTransfers_of_continuation (N r ell : ℕ) (hN : 0 < N)
    (hm : ell + 1 < N * (r + 1)) : ExceptionalTransfers N r ell := by
  have : CharZero (FractionRing (R (r + 1))) := algebraRat.charZero _
  apply exceptionalTransfers_of_representatives N r ell hm
  intro s _
  exact Continuation.exists_exceptional_representative (FractionRing (R (r + 1))) hN hm s

end TorusLinkHomology.CoefficientComplex
