import TorusLinkHomology.Generation.UniversalTransferEvaluation
import TorusLinkHomology.Generation.UniversalConnectingSpecialization

/-!
# Finishing exceptional transfers from the free chain identity

Only a nonzero rational scalar is divided out. The second part records the
precise increasing enumeration of a finite exceptional index set, including
the selector's degree and the nonvanishing of its rational transfer scalar.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.UniversalTransferSpecialization

open CoefficientComplex

/-- The explicit free chain identity supplies an actual tail representative.
The rescaling uses only the inverse of its nonzero rational coefficient. -/
theorem specialize_omega_mem_tailRepresentativeSpace_of_identity
    (N m r ell q : ℕ) (hN : 0 < N) (hm : 0 < m) (hbound : N * r = ell + m)
    (t : Fin (q + 1) → ℕ) (a : ℚ) (ha : a ≠ 0)
    (c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1))
    (i : ℕ) (B : UniversalTransfer.A)
    (hidentity : a • UniversalTransfer.omega N m q t =
      UniversalTransfer.d N m B + ((-1 : ℚ) ^ (q + 1)) •
        ((UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
          UniversalTransfer.ySeries (UniversalTransfer.pSeries N m r)).coeff i)) :
    specialize N r ell (UniversalTransfer.omega N m q t) ∈
      tailRepresentativeSpace N r ell := by
  have hspec := congrArg (specialize N r ell) hidentity
  rw [map_rat_smul, map_add, map_rat_smul] at hspec
  have hmdef : m = N * r - ell := by omega
  have hd : specialize N r ell (UniversalTransfer.d N m B) =
      CoefficientComplex.d N r ell (specialize N r ell B) := by
    rw [hmdef]
    exact (d_specialize N r ell (by omega) B).symm
  rw [hd] at hspec
  have hjet := specialize_jetExpression_pSeries_coeff_mem_tailSubalgebra
    N m r ell hN hm hbound c i
  have hscaled : a • specialize N r ell (UniversalTransfer.omega N m q t) ∈
      tailRepresentativeSpace N r ell := by
    rw [hspec]
    refine ⟨((-1 : ℚ) ^ (q + 1)) • specialize N r ell
      ((UniversalJets.jetExpression N c (r : ℤ) (((N + 1) * r : ℕ) : ℤ)
        UniversalTransfer.ySeries (UniversalTransfer.pSeries N m r)).coeff i), ?_,
      specialize N r ell B, add_comm _ _⟩
    exact (tailSubalgebra N r ell).toSubmodule.restrictScalars ℚ |>.smul_mem _ hjet
  have hrescale := ((tailRepresentativeSpace N r ell).restrictScalars ℚ).smul_mem a⁻¹ hscaled
  change a⁻¹ • (a • specialize N r ell (UniversalTransfer.omega N m q t)) ∈
    tailRepresentativeSpace N r ell at hrescale
  simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hrescale

/-- The actual natural-number deficit set of a finite family of bounded indices. -/
def deficitSet {k : ℕ} (s : Finset (Fin k)) : Finset ℕ := s.image Fin.val

@[simp] theorem card_deficitSet {k : ℕ} (s : Finset (Fin k)) :
    (deficitSet s).card = s.card := Finset.card_image_of_injective s Fin.val_injective

theorem deficitSet_subset_range {k : ℕ} (s : Finset (Fin k)) :
    deficitSet s ⊆ Finset.range k := by
  rintro t ht
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
  exact Finset.mem_range.mpr j.isLt

@[simp] theorem deficitSet_nonempty {k : ℕ} (s : Finset (Fin k)) :
    (deficitSet s).Nonempty ↔ s.Nonempty := Finset.image_nonempty

theorem card_deficitSet_le {k : ℕ} (s : Finset (Fin k)) : (deficitSet s).card ≤ k := by
  simpa only [Finset.card_range] using Finset.card_le_card (deficitSet_subset_range s)

/-- Taking values of the increasing bounded enumeration preserves its order exactly. -/
theorem orderEmbOfFin_deficitSet {k q : ℕ} (s : Finset (Fin k)) (hs : s.card = q) :
    (fun i => (s.orderEmbOfFin hs i).val) =
      (deficitSet s).orderEmbOfFin ((card_deficitSet s).trans hs) := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    exact Finset.mem_image.mpr ⟨s.orderEmbOfFin hs i, s.orderEmbOfFin_mem hs i, rfl⟩
  · intro i j hij
    exact (s.orderEmbOfFin hs).strictMono hij

/-- The chosen series coefficient is the sum of the same deficits in either convention. -/
theorem sum_deficitSet {k : ℕ} (s : Finset (Fin k)) :
    ∑ t ∈ deficitSet s, t = ∑ j ∈ s, j.val := by
  apply Finset.sum_image
  intro x _ y _ hxy
  exact Fin.ext hxy

/-- The exceptional selector has degree k minus the size of the selected set. -/
theorem natDegree_selector_deficitSet {k : ℕ} (b : ℤ) (s : Finset (Fin k)) :
    (CoefficientSelector.selector b k (deficitSet s)).natDegree = k - s.card := by
  rw [CoefficientSelector.natDegree_selector_of_subset b k _ (deficitSet_subset_range s),
    card_deficitSet]

theorem natDegree_selector_add_card {k : ℕ} (b : ℤ) (s : Finset (Fin k)) :
    (CoefficientSelector.selector b k (deficitSet s)).natDegree + s.card = k := by
  rw [natDegree_selector_deficitSet]
  apply Nat.sub_add_cancel
  simpa only [card_deficitSet] using card_deficitSet_le s

/-- A nonempty exceptional product has at most N factors. -/
theorem exceptional_card_le (N r ell q : ℕ)
    (s : Finset (Fin (exceptionalCount N r ell))) (hs : s.card = q + 1) :
    q + 1 ≤ N := by
  have hcard := card_deficitSet_le s
  rw [card_deficitSet, hs] at hcard
  exact hcard.trans (Nat.min_le_left _ _)

/-- This is the precise finite-jet derivative bound required by the universal identity. -/
theorem exceptional_selector_degree_bound (N r ell q : ℕ) (b : ℤ)
    (s : Finset (Fin (exceptionalCount N r ell))) (hs : s.card = q + 1) :
    (CoefficientSelector.selector b (exceptionalCount N r ell) (deficitSet s)).natDegree +
      (q + 1) ≤ N := by
  rw [← hs, natDegree_selector_add_card]
  exact Nat.min_le_left _ _

/-- The transfer coefficient of every actual exceptional subset is a nonzero rational number. -/
theorem exceptional_transferScalar_ne_zero (N r ell : ℕ)
    (s : Finset (Fin (exceptionalCount N r ell))) :
    CoefficientSelector.transferScalar (N * (r + 1) - (ell + 1))
      (exceptionalCount N r ell) (deficitSet s) ≠ 0 :=
  CoefficientSelector.transferScalar_ne_zero _ _ _ (Nat.min_le_right _ _)

/-- The selected increasing deficits meet both strict exceptional bounds. -/
theorem exceptional_deficit_bounds (N r ell : ℕ)
    (s : Finset (Fin (exceptionalCount N r ell))) {t : ℕ} (ht : t ∈ deficitSet s) :
    t < N ∧ t < N * (r + 1) - (ell + 1) := by
  have hk := Finset.mem_range.mp (deficitSet_subset_range s ht)
  exact ⟨hk.trans_le (Nat.min_le_left _ _), hk.trans_le (Nat.min_le_right _ _)⟩

/-- Reindexing the free identity by natural-number deficits gives the literal
specialized omega used by the connecting representative theorem. The extracted
coefficient includes the shift m of the V term in dC. -/
theorem exceptional_omega_mem_of_deficit_identity (N r ell q : ℕ)
    (hN : 0 < N) (hm : ell + 1 < N * (r + 1))
    (s : Finset (Fin (exceptionalCount N r ell))) (hs : s.card = q + 1)
    (c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1))
    (B : UniversalTransfer.A)
    (hidentity :
      CoefficientSelector.transferScalar (N * (r + 1) - (ell + 1))
        (exceptionalCount N r ell) (deficitSet s) •
        UniversalTransfer.omega N (N * (r + 1) - (ell + 1)) q
          ((deficitSet s).orderEmbOfFin ((card_deficitSet s).trans hs)) =
      UniversalTransfer.d N (N * (r + 1) - (ell + 1)) B +
        ((-1 : ℚ) ^ (q + 1)) •
          ((UniversalJets.jetExpression N c (r + 1 : ℕ) (((N + 1) * (r + 1) : ℕ) : ℤ)
            UniversalTransfer.ySeries
            (UniversalTransfer.pSeries N (N * (r + 1) - (ell + 1)) (r + 1))).coeff
              (N * (r + 1) - (ell + 1) + ∑ t ∈ deficitSet s, t))) :
    specialize N (r + 1) (ell + 1)
      (UniversalTransfer.omega N (N * (r + 1) - (ell + 1)) q
        (fun i => (s.orderEmbOfFin hs i).val)) ∈
      tailRepresentativeSpace N (r + 1) (ell + 1) := by
  rw [orderEmbOfFin_deficitSet s hs]
  exact specialize_omega_mem_tailRepresentativeSpace_of_identity
    N (N * (r + 1) - (ell + 1)) (r + 1) (ell + 1) q hN (by omega) (by omega)
    _ _ (exceptional_transferScalar_ne_zero N r ell s) c _ B hidentity

end TorusLinkHomology.UniversalTransferSpecialization
