import TorusLinkHomology.HilbertSeries.AuxiliaryRecurrence
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Module.LinearMap.Rat

/-! The rational linear connecting map and exactness on actual homology. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace TorusLinkHomology.CoefficientComplex

/-- Canonical-lift connecting cycles. Their images under J are the differential
of ξ₀ times the common-variable lift, as in the comparison proof. -/
def connectingCycle (N r ell : ℕ) (hm : ell + 1 < N * (r + 1))
    (a : (dga N r (ell + 1)).cycles) : (dga N (r + 1) (ell + 1)).cycles :=
  ⟨(connecting_representative N r ell hm a a.property).choose,
    (connecting_representative N r ell hm a a.property).choose_spec.1⟩

theorem J_connectingCycle (N r ell : ℕ) (hm : ell + 1 < N * (r + 1))
    (a : (dga N r (ell + 1)).cycles) :
    J N (r + 1) (ell + 1) (connectingCycle N r ell hm a) =
      d N (r + 1) ell (xi (r + 1) 0 * includeCommon r a) :=
  (connecting_representative N r ell hm a a.property).choose_spec.2

theorem connectingCycle_representative (N r ell : ℕ) (hm : ell + 1 < N * (r + 1))
    (a : (dga N r (ell + 1)).cycles) :
    ConnectingRepresentative N r ell a (connectingCycle N r ell hm a) :=
  ⟨xi (r + 1) 0 * includeCommon r a, p_lift r a, J_connectingCycle N r ell hm a⟩

/-- The canonical connecting lift is rational linear already on cycles. -/
def connectingCycles (N r ell : ℕ) (hm : ell + 1 < N * (r + 1)) :
    (dga N r (ell + 1)).cycles →ₗ[ℚ] (dga N (r + 1) (ell + 1)).cycles where
  toFun := connectingCycle N r ell hm
  map_add' a b := by
    apply Subtype.ext
    apply J_injective N r ell hm
    change J N (r + 1) (ell + 1) (connectingCycle N r ell hm (a + b)).val =
      J N (r + 1) (ell + 1) ((connectingCycle N r ell hm a).val + (connectingCycle N r ell hm b).val)
    rw [map_add, J_connectingCycle, J_connectingCycle, J_connectingCycle]
    change d N (r + 1) ell (xi (r + 1) 0 * includeCommon r (a.val + b.val)) = _
    rw [map_add, mul_add, map_add]
  map_smul' c a := by
    apply Subtype.ext
    apply J_injective N r ell hm
    change J N (r + 1) (ell + 1) (connectingCycle N r ell hm (c • a)).val =
      J N (r + 1) (ell + 1) (c • (connectingCycle N r ell hm a).val)
    rw [map_rat_smul, J_connectingCycle, J_connectingCycle]
    change d N (r + 1) ell (xi (r + 1) 0 * includeCommon r (c • a.val)) = _
    rw [map_rat_smul, mul_smul_comm, map_rat_smul]

/-- The source homology quotient map with rational scalars. -/
def auxiliaryClassMap (N r ell : ℕ) :
    (dga N r ell).cycles →ₗ[ℚ] (dga N r ell).Homology :=
  (dga N r ell).homologyClass.toLinearMap.restrictScalars ℚ

theorem auxiliaryClassMap_surjective (N r ell : ℕ) :
    Function.Surjective (auxiliaryClassMap N r ell) :=
  (dga N r ell).homologyClass_surjective

/-- Connecting cycles followed by their actual homology classes. -/
def connectingCycleClass (N r ell : ℕ) (hm : ell + 1 < N * (r + 1)) :
    (dga N r (ell + 1)).cycles →ₗ[ℚ] (dga N (r + 1) (ell + 1)).Homology :=
  (auxiliaryClassMap N (r + 1) (ell + 1)).comp (connectingCycles N r ell hm)

private theorem connectingCycleClass_boundary (N r ell : ℕ)
    (hm : ell + 1 < N * (r + 1)) :
    LinearMap.ker (auxiliaryClassMap N r (ell + 1)) ≤
      LinearMap.ker (connectingCycleClass N r ell hm) := by
  intro a ha
  change (dga N r (ell + 1)).homologyClass a = 0 at ha
  obtain ⟨q, hq⟩ := (dga N r (ell + 1)).homologyClass_eq_zero_iff a |>.mp ha
  change (dga N (r + 1) (ell + 1)).homologyClass (connectingCycle N r ell hm a) = 0
  apply (dga N (r + 1) (ell + 1)).homologyClass_eq_zero_iff _ |>.mpr
  have hz := connectingCycle_representative N r ell hm a
  rw [← hq] at hz
  obtain ⟨c, hc⟩ := hz.boundary_of_source_boundary hm
  exact ⟨c, hc.symm⟩

/-- The connecting map on homology, constructed through the rational quotient. -/
def connectingHomology (N r ell : ℕ) (hm : ell + 1 < N * (r + 1)) :
    (dga N r (ell + 1)).Homology →ₗ[ℚ] (dga N (r + 1) (ell + 1)).Homology :=
  ((LinearMap.ker (auxiliaryClassMap N r (ell + 1))).liftQ
    (connectingCycleClass N r ell hm) (connectingCycleClass_boundary N r ell hm)).comp
    ((auxiliaryClassMap N r (ell + 1)).quotKerEquivOfSurjective
      (auxiliaryClassMap_surjective N r (ell + 1))).symm.toLinearMap

@[simp] theorem connectingHomology_class (N r ell : ℕ) (hm : ell + 1 < N * (r + 1))
    (a : (dga N r (ell + 1)).cycles) :
    connectingHomology N r ell hm ((dga N r (ell + 1)).homologyClass a) =
      (dga N (r + 1) (ell + 1)).homologyClass (connectingCycle N r ell hm a) := by
  change connectingHomology N r ell hm ((auxiliaryClassMap N r (ell + 1)) a) = _
  unfold connectingHomology
  change (LinearMap.ker (auxiliaryClassMap N r (ell + 1))).liftQ
    (connectingCycleClass N r ell hm) (connectingCycleClass_boundary N r ell hm)
    (((auxiliaryClassMap N r (ell + 1)).quotKerEquivOfSurjective
      (auxiliaryClassMap_surjective N r (ell + 1))).symm ((auxiliaryClassMap N r (ell + 1)) a)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- Any lift diagram computes the connecting homology class. -/
theorem connectingHomology_eq_class (N r ell : ℕ) (hm : ell + 1 < N * (r + 1))
    (a : (dga N r (ell + 1)).cycles) (z : (dga N (r + 1) (ell + 1)).cycles)
    (hz : ConnectingRepresentative N r ell a z) :
    connectingHomology N r ell hm ((dga N r (ell + 1)).homologyClass a) =
      (dga N (r + 1) (ell + 1)).homologyClass z := by
  rw [connectingHomology_class]
  apply (dga N (r + 1) (ell + 1)).homologyClass_eq_iff _ _ |>.mpr
  obtain ⟨c, hc⟩ := (connectingCycle_representative N r ell hm a).eq_mod_boundary hm hz
  exact ⟨c, by change d N (r + 1) (ell + 1) c = _; rw [hc]; abel⟩

/-- Generation makes the connecting homology map injective. -/
theorem connectingHomology_injective (N r ell : ℕ) (hN : 0 < N)
    (hm : ell + 1 < N * (r + 1)) : Function.Injective (connectingHomology N r ell hm) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  change connectingHomology N r ell hm x = 0 at hx
  change x = 0
  obtain ⟨a, rfl⟩ := (dga N r (ell + 1)).homologyClass_surjective x
  rw [connectingHomology_class] at hx
  obtain ⟨c, hc⟩ := (dga N (r + 1) (ell + 1)).homologyClass_eq_zero_iff _ |>.mp hx
  obtain ⟨q, hq⟩ := (connecting_boundary_iff N r ell hN hm
    (connectingCycle_representative N r ell hm a)).mp ⟨c, hc.symm⟩
  exact (dga N r (ell + 1)).homologyClass_eq_zero_iff a |>.mpr ⟨q, hq.symm⟩

/-- Exactness at new homology, now an equality of rational submodules. -/
theorem range_connectingHomology (N r ell : ℕ) (hm : ell + 1 < N * (r + 1)) :
    LinearMap.range (connectingHomology N r ell hm) =
      LinearMap.ker ((comparisonHomology N (r + 1) (ell + 1)).restrictScalars ℚ) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    obtain ⟨a, rfl⟩ := (dga N r (ell + 1)).homologyClass_surjective y
    rw [connectingHomology_class]
    change comparisonHomology N (r + 1) (ell + 1)
      ((dga N (r + 1) (ell + 1)).homologyClass (connectingCycle N r ell hm a)) = 0
    rw [comparisonHomology_class]
    apply (dga N (r + 1) (ell + 1 - 1)).homologyClass_eq_zero_iff _ |>.mpr
    refine ⟨xi (r + 1) 0 * includeCommon r a, ?_⟩
    change d N (r + 1) (ell + 1 - 1) _ = J N (r + 1) (ell + 1) _
    rw [Nat.add_sub_cancel_right]
    exact (J_connectingCycle N r ell hm a).symm
  · intro x hx
    change comparisonHomology N (r + 1) (ell + 1) x = 0 at hx
    obtain ⟨z, rfl⟩ := (dga N (r + 1) (ell + 1)).homologyClass_surjective x
    rw [comparisonHomology_class] at hx
    obtain ⟨w, hw⟩ := (dga N (r + 1) (ell + 1 - 1)).homologyClass_eq_zero_iff _ |>.mp hx
    change d N (r + 1) (ell + 1 - 1) w = J N (r + 1) (ell + 1) z at hw
    have hw' : J N (r + 1) (ell + 1) z = d N (r + 1) ell w := by
      simpa only [Nat.add_sub_cancel_right] using hw.symm
    obtain ⟨a, ha, hz⟩ := (exists_connectingRepresentative_iff N r ell z).mpr ⟨w, hw'⟩
    exact ⟨(dga N r (ell + 1)).homologyClass ⟨a, ha⟩,
      connectingHomology_eq_class N r ell hm ⟨a, ha⟩ z hz⟩

end TorusLinkHomology.CoefficientComplex
