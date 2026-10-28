import TorusLinkHomology.HilbertSeries.ReversalDecomposition
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Homology of the passive-monomial decomposition. All maps are over ℚ;
the coefficient rings of the active and auxiliary complexes may differ. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries.GeneralReversal

/-- Extract one active cycle from an auxiliary cycle. -/
def componentCycle (N m p : ℕ) (hN : 0 < N) (t : ChainIndex p) :
    (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).cycles →ₗ[ℚ]
      (torusLinkDGA N m).cycles where
  toFun z := ⟨decomposeChains m p z.val t,
    (auxiliary_cycle_iff_components N m p hN z.val).mp z.property t⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)

/-- The homology class of an active component. -/
def componentClass (N m p : ℕ) (hN : 0 < N) (t : ChainIndex p) :
    (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).cycles →ₗ[ℚ] Homology N m :=
  ((torusLinkDGA N m).homologyClass.toLinearMap.restrictScalars ℚ).comp
    (componentCycle N m p hN t)

/-- All active homology classes, with finite support inherited from a cycle. -/
def cycleClasses (N m p : ℕ) (hN : 0 < N) :
    (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).cycles →ₗ[ℚ]
      (ChainIndex p →₀ Homology N m) where
  toFun z := by
    classical
    exact Finsupp.onFinset (decomposeChains m p z.val).support
      (fun t => componentClass N m p hN t z) (by
        intro t ht
        apply Finsupp.mem_support_iff.mpr
        intro he
        have hz : componentCycle N m p hN t z = 0 := Subtype.ext he
        exact ht (by change (torusLinkDGA N m).homologyClass _ = 0; rw [hz, map_zero]))
  map_add' x y := by
    classical
    ext t
    exact map_add (componentClass N m p hN t) x y
  map_smul' c x := by
    classical
    ext t
    exact map_smul (componentClass N m p hN t) c x

@[simp] theorem cycleClasses_apply (N m p : ℕ) (hN : 0 < N)
    (z : (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).cycles) (t : ChainIndex p) :
    cycleClasses N m p hN z t = (torusLinkDGA N m).homologyClass (componentCycle N m p hN t z) := rfl

/-- Boundaries have zero class in every active summand. -/
theorem boundaries_le_ker_cycleClasses (N m p : ℕ) (hN : 0 < N) :
    (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).boundaries.restrictScalars ℚ ≤
      LinearMap.ker (cycleClasses N m p hN) := by
  intro z hz
  obtain ⟨u, hu⟩ := (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).mem_boundaries z |>.mp hz
  ext t
  apply (torusLinkDGA N m).homologyClass_eq_zero_iff _ |>.mpr
  refine ⟨decomposeChains m p u t, ?_⟩
  have he := DFunLike.congr_fun (decomposeChains_d N m p hN u) t
  change decomposeChains m p _ t = d N m _ at he
  change d N m _ = decomposeChains m p z.val t
  rw [← he, hu]

/-- Regard auxiliary homology as the rational quotient of its cycles. -/
def auxiliaryHomologyQuotient (N m p : ℕ) :
    (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).Homology ≃ₗ[ℚ]
      (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).cycles ⧸
        (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).boundaries.restrictScalars ℚ :=
  (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).homologyModuleEquiv.restrictScalars ℚ ≪≫ₗ
    (Submodule.Quotient.restrictScalarsEquiv ℚ _).symm

/-- Decomposition of auxiliary homology into active homology classes. -/
def decomposeHomology (N m p : ℕ) (hN : 0 < N) :
    (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).Homology →ₗ[ℚ]
      (ChainIndex p →₀ Homology N m) :=
  ((CoefficientComplex.dga N (m + p) (N * (m + p) - m)).boundaries.restrictScalars ℚ).liftQ
    (cycleClasses N m p hN) (boundaries_le_ker_cycleClasses N m p hN) |>.comp
      (auxiliaryHomologyQuotient N m p).toLinearMap

@[simp] theorem decomposeHomology_class (N m p : ℕ) (hN : 0 < N)
    (z : (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).cycles) :
    decomposeHomology N m p hN
      ((CoefficientComplex.dga N (m + p) (N * (m + p) - m)).homologyClass z) =
      cycleClasses N m p hN z := by
  simp [decomposeHomology, auxiliaryHomologyQuotient]

/-- Vanishing of all active classes supplies a finite sum of active primitives. -/
theorem ker_cycleClasses_le_boundaries (N m p : ℕ) (hN : 0 < N) :
    LinearMap.ker (cycleClasses N m p hN) ≤
      (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).boundaries.restrictScalars ℚ := by
  classical
  intro z hz
  have hprim (t : ChainIndex p) : ∃ u : A m, d N m u = decomposeChains m p z.val t := by
    apply (torusLinkDGA N m).homologyClass_eq_zero_iff (componentCycle N m p hN t z) |>.mp
    exact DFunLike.congr_fun hz t
  choose u hu using hprim
  let f := decomposeChains m p z.val
  let g : ChainIndex p →₀ A m := ∑ t ∈ f.support, Finsupp.single t (u t)
  have hg : Finsupp.mapRange (d N m) (map_zero _) g = f := by
    change (Finsupp.mapRange.linearMap ((d N m).restrictScalars ℚ)) g = f
    dsimp only [g]
    simp only [map_sum, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, LinearMap.restrictScalars_apply, hu]
    exact Finsupp.sum_single f
  apply (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).mem_boundaries z |>.mpr
  refine ⟨(decomposeChains m p).symm g, ?_⟩
  rw [d_decomposeChains_symm N m p hN, hg]
  exact (decomposeChains m p).symm_apply_apply z.val

/-- Insert a cycle in a single passive-monomial summand. -/
def includeCycle (N m p : ℕ) (hN : 0 < N) (t : ChainIndex p) :
    (torusLinkDGA N m).cycles →ₗ[ℚ]
      (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).cycles where
  toFun z := ⟨(decomposeChains m p).symm (Finsupp.single t z.val), by
    change CoefficientComplex.d N (m + p) (N * (m + p) - m) _ = 0
    rw [d_decomposeChains_symm_single N m p hN]
    change (decomposeChains m p).symm (Finsupp.single t ((torusLinkDGA N m).d z.val)) = 0
    rw [z.property, Finsupp.single_zero, map_zero]⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := by
    apply Subtype.ext
    change (decomposeChains m p).symm (Finsupp.single t (c • x.val)) =
      c • (decomposeChains m p).symm (Finsupp.single t x.val)
    rw [← Finsupp.smul_single, map_smul]

@[simp] theorem cycleClasses_includeCycle (N m p : ℕ) (hN : 0 < N) (t : ChainIndex p)
    (z : (torusLinkDGA N m).cycles) :
    cycleClasses N m p hN (includeCycle N m p hN t z) =
      Finsupp.single t ((torusLinkDGA N m).homologyClass z) := by
  classical
  ext j
  rw [cycleClasses_apply]
  have hc : componentCycle N m p hN j (includeCycle N m p hN t z) =
      if t = j then z else 0 := by
    apply Subtype.ext
    change decomposeChains m p ((decomposeChains m p).symm (Finsupp.single t z.val)) j = _
    rw [LinearEquiv.apply_symm_apply]
    split_ifs <;> simp_all
  rw [hc]
  split_ifs <;> simp_all

theorem decomposeHomology_surjective (N m p : ℕ) (hN : 0 < N) :
    Function.Surjective (decomposeHomology N m p hN) := by
  intro f
  induction f using Finsupp.induction with
  | zero => exact ⟨0, map_zero _⟩
  | single_add t x f ht hx ih =>
    obtain ⟨z, rfl⟩ := (torusLinkDGA N m).homologyClass_surjective x
    obtain ⟨q, hq⟩ := ih
    refine ⟨(CoefficientComplex.dga N (m + p) (N * (m + p) - m)).homologyClass
      (includeCycle N m p hN t z) + q, ?_⟩
    rw [map_add, decomposeHomology_class, cycleClasses_includeCycle, hq]

theorem decomposeHomology_injective (N m p : ℕ) (hN : 0 < N) :
    Function.Injective (decomposeHomology N m p hN) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨z, rfl⟩ := (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).homologyClass_surjective x
  rw [decomposeHomology_class] at hx
  have hz := ker_cycleClasses_le_boundaries N m p hN hx
  apply (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).homologyClass_eq_zero_iff z |>.mpr
  exact (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).mem_boundaries z |>.mp hz

/-- Auxiliary homology is a direct sum of original homology copies indexed by
passive polynomial/exterior monomials. This is proved directly from representatives. -/
def homologyDecomposition (N m p : ℕ) (hN : 0 < N) :
    (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).Homology ≃ₗ[ℚ]
      (ChainIndex p →₀ Homology N m) :=
  LinearEquiv.ofBijective (decomposeHomology N m p hN)
    ⟨decomposeHomology_injective N m p hN, decomposeHomology_surjective N m p hN⟩

end TorusLinkHomology.HilbertSeries.GeneralReversal
