import TorusLinkHomology.HilbertSeries.ReversalGrading
import TorusLinkHomology.HilbertSeries.HomologyProjection

/-! Homogeneous restrictions of the passive-monomial homology decomposition. -/
noncomputable section
set_option maxRecDepth 4000
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries.GeneralReversal

def componentHomology (N m p : ℕ) (hN : 0 < N) (t : ChainIndex p) :
    (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).Homology →ₗ[ℚ] Homology N m :=
  (Finsupp.lapply t).comp (decomposeHomology N m p hN)

def includeHomology (N m p : ℕ) (hN : 0 < N) (t : ChainIndex p) :
    Homology N m →ₗ[ℚ] (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).Homology :=
  (homologyDecomposition N m p hN).symm.toLinearMap.comp (Finsupp.lsingle t)

@[simp] theorem componentHomology_class (N m p : ℕ) (hN : 0 < N) (t : ChainIndex p)
    (z : (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).cycles) :
    componentHomology N m p hN t
      ((CoefficientComplex.dga N (m + p) (N * (m + p) - m)).homologyClass z) =
        (torusLinkDGA N m).homologyClass (componentCycle N m p hN t z) := by
  simp [componentHomology]

@[simp] theorem includeHomology_class (N m p : ℕ) (hN : 0 < N) (t : ChainIndex p)
    (z : (torusLinkDGA N m).cycles) :
    includeHomology N m p hN t ((torusLinkDGA N m).homologyClass z) =
      (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).homologyClass
        (includeCycle N m p hN t z) := by
  apply (homologyDecomposition N m p hN).injective
  change homologyDecomposition N m p hN ((homologyDecomposition N m p hN).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  change _ = decomposeHomology N m p hN _
  rw [decomposeHomology_class, cycleClasses_includeCycle]
  rfl

@[simp] theorem component_includeHomology (N m p : ℕ) (hN : 0 < N)
    (s t : ChainIndex p) (x : Homology N m) :
    componentHomology N m p hN s (includeHomology N m p hN t x) =
      if t = s then x else 0 := by
  classical
  change (homologyDecomposition N m p hN
    ((homologyDecomposition N m p hN).symm (Finsupp.single t x))) s = _
  rw [LinearEquiv.apply_symm_apply, Finsupp.single_apply]

/-- The component class has no tridegrees incompatible with its auxiliary degree. -/
theorem component_homologyProjection_eq_zero (N m p w h a b k : ℕ) (hN : 0 < N)
    {x : (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).Homology}
    (hx : x ∈ Auxiliary.homologyPiece N (N * (m + p) - m) (m + p) w h)
    (t : ChainIndex p)
    (hne : ¬ (passiveWeight N m p t + (m + p) * a = w + b ∧ k + t.2.card = h)) :
    homologyProjection N m a b k (componentHomology N m p hN t x) = 0 := by
  obtain ⟨z, hz, rfl⟩ := hx
  change homologyProjection N m a b k (componentHomology N m p hN t
    ((CoefficientComplex.dga N (m + p) (N * (m + p) - m)).homologyClass z)) = 0
  rw [componentHomology_class, homologyProjection_class]
  have he : cycleProjection N m a b k (componentCycle N m p hN t z) = 0 := by
    apply Subtype.ext
    exact component_projection_eq_zero N m p w h a b k hN hz t hne
  rw [he, map_zero]

/-- Each compatible homogeneous original class includes in the stated auxiliary piece. -/
theorem includeHomology_mem (N m p w h a b k : ℕ) (hN : 0 < N)
    (t : ChainIndex p) (hb : b ≤ (m + p) * a)
    (hw : passiveWeight N m p t + (m + p) * a = w + b)
    (hh : k + t.2.card = h) {x : Homology N m} (hx : x ∈ homologyPiece N m a b k) :
    includeHomology N m p hN t x ∈
      Auxiliary.homologyPiece N (N * (m + p) - m) (m + p) w h := by
  obtain ⟨z, hz, rfl⟩ := hx
  change includeHomology N m p hN t ((torusLinkDGA N m).homologyClass z) ∈ _
  rw [includeHomology_class]
  refine ⟨includeCycle N m p hN t z, ?_, rfl⟩
  change (decomposeChains m p).symm (Finsupp.single t z.val) ∈
    Auxiliary.chainPiece (N * (m + p) - m) (m + p) w h
  rw [decomposeChains_symm_single]
  change z.val ∈ chainPiece N m a b k at hz
  have ha := activeChains_mem N m (m + p) a b k ((m + p) * a - b) hN
    (Nat.le_add_right m p) (Nat.sub_add_cancel hb) hz
  have hp := passiveMonomial_mem N m p hN t
  have hm := Auxiliary.mul_mem_chainPiece ha hp
  have hw' : (m + p) * a - b + passiveWeight N m p t = w := by omega
  simpa only [hw', hh] using hm

/-- Each passive polynomial exponent is bounded by the passive weight. -/
theorem passive_exponent_le_weight (N m p : ℕ) (t : ChainIndex p) (i : Fin p) :
    t.1 i ≤ passiveWeight N m p t := by
  have hs := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin p))) => Nat.zero_le ((j.val + 1) * t.1 j))
    (Finset.mem_univ i)
  have hi : t.1 i ≤ (i.val + 1) * t.1 i := le_mul_of_one_le_left (Nat.zero_le _) (by omega)
  unfold passiveWeight
  omega

/-- Nonzero homogeneous components lie in a finite coefficient-dependent box. -/
theorem component_projection_bounds (N m p C w h a b k : ℕ) (hN : 0 < N)
    (hC : m - 1 ≤ C) (hr : C < m + p)
    {x : (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).Homology}
    (hx : x ∈ Auxiliary.homologyPiece N (N * (m + p) - m) (m + p) w h)
    (t : ChainIndex p)
    (hne : homologyProjection N m a b k (componentHomology N m p hN t x) ≠ 0) :
    (∀ i, t.1 i ≤ w) ∧ a ≤ w ∧ b ≤ C * w ∧ k ≤ h ∧
      passiveWeight N m p t + (m + p) * a = w + b ∧ k + t.2.card = h ∧ b ≤ C * a := by
  have hc : passiveWeight N m p t + (m + p) * a = w + b ∧ k + t.2.card = h := by
    by_contra hn
    exact hne (component_homologyProjection_eq_zero N m p w h a b k hN hx t hn)
  have hb : b ≤ (m - 1) * a := by
    by_contra hn
    have hz := homologyPiece_eq_bot_of_chainPiece_eq_bot (h := k)
      (chainPiece_eq_bot_of_weight_bound hN (Nat.lt_of_not_ge hn))
    have hp := homologyProjection_mem N m a b k (componentHomology N m p hN t x)
    rw [hz] at hp
    exact hne hp
  have hbC : b ≤ C * a := hb.trans (Nat.mul_le_mul_right a hC)
  have hca : (C + 1) * a ≤ (m + p) * a := Nat.mul_le_mul_right a hr
  have haw : passiveWeight N m p t + a ≤ w := by nlinarith [hc.1]
  refine ⟨?_, by omega, ?_, by omega, hc.1, hc.2, hbC⟩
  · intro i
    exact (passive_exponent_le_weight N m p t i).trans (by omega)
  · exact hbC.trans (Nat.mul_le_mul_left C (by omega))

end TorusLinkHomology.HilbertSeries.GeneralReversal
