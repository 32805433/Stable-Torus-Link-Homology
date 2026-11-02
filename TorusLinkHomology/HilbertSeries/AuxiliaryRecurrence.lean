import TorusLinkHomology.Generation.AuxiliaryInduction
import TorusLinkHomology.Generation.ChainIdentity
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Representative-level short exactness for the auxiliary homology recurrence.
The weight-space dimension calculation is a separate obligation. -/

noncomputable section
namespace TorusLinkHomology.CoefficientComplex

/-- The existing generation proof, specialized for use in the comparison sequence. -/
theorem hilbert_tailGeneration (N : ℕ) (hN : 0 < N) (r ell : ℕ) :
    TailGeneration N r ell :=
  tailGeneration_of_all_exceptionalTransfers N hN
    (fun r ell hm => exceptionalTransfers_of_continuation N r ell hN hm) r ell

/-- Every old cycle lifts modulo a boundary to a new cycle. -/
theorem comparison_cycle_lift (N r ell : ℕ) (hN : 0 < N)
    (hell : ell ≤ N * r) (z : A r) (hz : d N r (ell - 1) z = 0) :
    ∃ v : A r, d N r ell v = 0 ∧ ∃ w : A r,
      z = J N r ell v + d N r (ell - 1) w := by
  obtain ⟨t, ht, w, hw⟩ := hilbert_tailGeneration N hN r (ell - 1) z hz
  rw [← J_tailSubalgebra N r ell hell, Subalgebra.mem_map] at ht
  obtain ⟨v, hv, hJv⟩ := ht
  exact ⟨v, tailSubalgebra_le_cycles N r ell hv, w, hJv ▸ hw⟩

/-- The comparison map on cycles, over the common polynomial coefficient ring. -/
def comparisonCycles (N r ell : ℕ) :
    (dga N r ell).cycles →ₗ[R r] (dga N r (ell - 1)).cycles where
  toFun z := ⟨J N r ell z, J_cycle N r ell z.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

private theorem comparisonCycles_boundary (N r ell : ℕ) :
    (dga N r ell).boundaries ≤ LinearMap.ker
      ((dga N r (ell - 1)).homologyClass.toLinearMap.comp (comparisonCycles N r ell)) := by
  intro z hz
  obtain ⟨c, hc⟩ := (dga N r ell).mem_boundaries z |>.mp hz
  apply (dga N r (ell - 1)).homologyClass_eq_zero_iff _ |>.mpr
  refine ⟨J N r ell c, ?_⟩
  change d N r (ell - 1) (J N r ell c) = J N r ell z
  rw [d_J]
  exact congrArg (J N r ell) hc

set_option synthInstance.maxHeartbeats 200000 in
/-- The comparison map on actual homology quotients. Restricting scalars gives
its rational linear map for weight-space dimension calculations. -/
def comparisonHomology (N r ell : ℕ) :
    (dga N r ell).Homology →ₗ[R r] (dga N r (ell - 1)).Homology :=
  ((dga N r ell).boundaries.liftQ
    ((dga N r (ell - 1)).homologyClass.toLinearMap.comp (comparisonCycles N r ell))
    (comparisonCycles_boundary N r ell)).comp
    (dga N r ell).homologyModuleEquiv.toLinearMap

@[simp] theorem comparisonHomology_class (N r ell : ℕ) (z : (dga N r ell).cycles) :
    comparisonHomology N r ell ((dga N r ell).homologyClass z) =
      (dga N r (ell - 1)).homologyClass (comparisonCycles N r ell z) := by
  simp [comparisonHomology]

theorem comparisonHomology_surjective (N r ell : ℕ) (hN : 0 < N)
    (hell : ell ≤ N * r) : Function.Surjective (comparisonHomology N r ell) := by
  intro x
  obtain ⟨z, rfl⟩ := (dga N r (ell - 1)).homologyClass_surjective x
  obtain ⟨v, hv, w, hw⟩ := comparison_cycle_lift N r ell hN hell z z.property
  refine ⟨(dga N r ell).homologyClass ⟨v, hv⟩, ?_⟩
  rw [comparisonHomology_class]
  apply (dga N r (ell - 1)).homologyClass_eq_iff _ _ |>.mpr
  refine ⟨-w, ?_⟩
  change d N r (ell - 1) (-w) = J N r ell v - z.val
  rw [map_neg, hw]
  abel

/-- Projection sends every middle cycle to a boundary in the quotient. -/
theorem comparison_projection_boundary (N r ell : ℕ) (hN : 0 < N)
    (hell : ell + 1 ≤ N * (r + 1)) (z : A (r + 1)) (hz : d N (r + 1) ell z = 0) :
    ∃ q : A r, p r z = d N r (ell + 1) q := by
  obtain ⟨v, _, w, hw⟩ := comparison_cycle_lift N (r + 1) (ell + 1) hN hell z
    (by simpa only [Nat.add_sub_cancel_right] using hz)
  refine ⟨-p r w, ?_⟩
  rw [hw, p_add, p_J, Nat.add_sub_cancel_right, p_d, zero_add, map_neg]

/-- Injectivity of the connecting map, expressed without choices of representatives. -/
theorem connecting_source_boundary_of_boundary (N r ell : ℕ) (hN : 0 < N)
    (hm : ell + 1 < N * (r + 1)) {a : A r} {z : A (r + 1)}
    (hz : ConnectingRepresentative N r ell a z)
    (hb : ∃ c, z = d N (r + 1) (ell + 1) c) :
    ∃ q : A r, a = d N r (ell + 1) q := by
  obtain ⟨w, hw, hzw⟩ := hz
  obtain ⟨c, rfl⟩ := hb
  have hcycle : d N (r + 1) ell (w - J N (r + 1) (ell + 1) c) = 0 := by
    have hdJ := d_J N (r + 1) (ell + 1) c
    simp only [Nat.add_sub_cancel_right] at hdJ
    rw [map_sub, hdJ, ← hzw, sub_self]
  obtain ⟨q, hq⟩ := comparison_projection_boundary N r ell hN (Nat.le_of_lt hm) _ hcycle
  refine ⟨q, ?_⟩
  have hp : p r (w - J N (r + 1) (ell + 1) c) = p r w := by
    unfold p
    rw [map_sub, map_sub]
    change p r w - p r (J N (r + 1) (ell + 1) c) = p r w
    rw [p_J, sub_zero]
  rwa [hp, hw] at hq

/-- The connecting class vanishes exactly when the source class vanishes. -/
theorem connecting_boundary_iff (N r ell : ℕ) (hN : 0 < N)
    (hm : ell + 1 < N * (r + 1)) {a : A r} {z : A (r + 1)}
    (hz : ConnectingRepresentative N r ell a z) :
    (∃ c, z = d N (r + 1) (ell + 1) c) ↔ ∃ q, a = d N r (ell + 1) q := by
  constructor
  · exact connecting_source_boundary_of_boundary N r ell hN hm hz
  · rintro ⟨q, rfl⟩
    exact hz.boundary_of_source_boundary hm

end TorusLinkHomology.CoefficientComplex
