import TorusLinkHomology.HilbertSeries.ReversalHomogeneous
import TorusLinkHomology.HilbertSeries.ReversalIndex
import TorusLinkHomology.HilbertSeries.FiniteDecomposition

/-! Finite homogeneous dimension convolution for the auxiliary reversal. -/
noncomputable section
set_option maxRecDepth 4000
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries.GeneralReversal

/-- Every nonzero projected component is represented by a bounded reversal index. -/
theorem exists_fiber_of_nonzero (N m p C w h a b k : ℕ) (hN : 0 < N)
    (hC : m - 1 ≤ C) (hr : C < m + p)
    {x : (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).Homology}
    (hx : x ∈ Auxiliary.homologyPiece N (N * (m + p) - m) (m + p) w h)
    (t : ChainIndex p)
    (hne : homologyProjection N m a b k (componentHomology N m p hN t x) ≠ 0) :
    ∃ i : ReversalFiber N m p C w h, i.passiveIndex = t ∧ i.degree = (a, b, k) := by
  obtain ⟨ht, ha, hb, hk, hw, hh, hs⟩ :=
    component_projection_bounds N m p C w h a b k hN hC hr hx t hne
  let bt : BoundedMonomial p w := (fun j => ⟨t.1 j, by have := ht j; omega⟩, t.2)
  have hbt : fiberPassiveIndex bt = t := by
    apply Prod.ext
    · ext j; rfl
    · rfl
  refine ⟨{
    passive := bt
    a := ⟨a, by omega⟩
    b := ⟨b, by omega⟩
    k := ⟨k, by omega⟩
    weight_eq := ?_
    degree_eq := hh
    support_bound := hs }, hbt, rfl⟩
  simpa only [hbt] using hw

abbrev reversalSourcePiece (N m p C w h : ℕ) (i : ReversalFiber N m p C w h) :=
  homologyPiece N m i.a.val i.b.val i.k.val

abbrev reversalTargetPiece (N m p w h : ℕ) :=
  Auxiliary.homologyPiece N (N * (m + p) - m) (m + p) w h

def fiberInclusion (N m p C w h : ℕ) (hN : 0 < N) (hr : C < m + p)
    (i : ReversalFiber N m p C w h) :
    reversalSourcePiece N m p C w h i →ₗ[ℚ] reversalTargetPiece N m p w h where
  toFun y := ⟨includeHomology N m p hN i.passiveIndex y.val,
    includeHomology_mem N m p w h i.a.val i.b.val i.k.val hN i.passiveIndex
      (i.support_bound.trans (Nat.mul_le_mul_right i.a.val (Nat.le_of_lt hr)))
      i.weight_eq i.degree_eq y.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

def fiberProjection (N m p C w h : ℕ) (hN : 0 < N) (i : ReversalFiber N m p C w h) :
    reversalTargetPiece N m p w h →ₗ[ℚ] reversalSourcePiece N m p C w h i where
  toFun x := ⟨homologyProjection N m i.a.val i.b.val i.k.val
    (componentHomology N m p hN i.passiveIndex x.val), homologyProjection_mem _ _ _ _ _ _⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)

theorem fiberProjection_inclusion (N m p C w h : ℕ) (hN : 0 < N) (hr : C < m + p)
    (i : ReversalFiber N m p C w h) (x : reversalSourcePiece N m p C w h i) :
    fiberProjection N m p C w h hN i (fiberInclusion N m p C w h hN hr i x) = x := by
  classical
  apply Subtype.ext
  change homologyProjection N m i.a.val i.b.val i.k.val
    (componentHomology N m p hN i.passiveIndex (includeHomology N m p hN i.passiveIndex x.val)) = x.val
  rw [component_includeHomology, if_pos rfl]
  exact homologyProjection_eq_self x.property

theorem fiberProjection_inclusion_ne (N m p C w h : ℕ) (hN : 0 < N) (hr : C < m + p)
    (i j : ReversalFiber N m p C w h) (hne : i ≠ j)
    (x : reversalSourcePiece N m p C w h j) :
    fiberProjection N m p C w h hN i (fiberInclusion N m p C w h hN hr j x) = 0 := by
  classical
  apply Subtype.ext
  change homologyProjection N m i.a.val i.b.val i.k.val
    (componentHomology N m p hN i.passiveIndex (includeHomology N m p hN j.passiveIndex x.val)) = 0
  rw [component_includeHomology]
  split_ifs with hp
  · apply homologyProjection_eq_zero_of_mem x.property
    intro hd
    exact hne (ReversalFiber.eq_of_passiveIndex_degree_eq hp hd).symm
  · exact map_zero _

theorem sum_include_component_projection (N m p C w h : ℕ) (hN : 0 < N)
    (hC : m - 1 ≤ C) (hr : C < m + p)
    {x : (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).Homology}
    (hx : x ∈ reversalTargetPiece N m p w h) :
    ∑ i : ReversalFiber N m p C w h, includeHomology N m p hN i.passiveIndex
      (homologyProjection N m i.a.val i.b.val i.k.val
        (componentHomology N m p hN i.passiveIndex x)) = x := by
  classical
  apply decomposeHomology_injective N m p hN
  ext t
  change componentHomology N m p hN t (∑ i : ReversalFiber N m p C w h, _) =
    componentHomology N m p hN t x
  rw [map_sum]
  simp only [component_includeHomology]
  let S : Finset (ReversalFiber N m p C w h) := Finset.univ.filter (fun i => i.passiveIndex = t)
  let T : Finset (ℕ × ℕ × ℕ) := S.image ReversalFiber.degree
  have hs : ∀ d ∉ T,
      homologyProjection N m d.1 d.2.1 d.2.2 (componentHomology N m p hN t x) = 0 := by
    intro d hd
    by_contra hn
    obtain ⟨i, hi, he⟩ := exists_fiber_of_nonzero N m p C w h d.1 d.2.1 d.2.2 hN hC hr hx t hn
    apply hd
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, he⟩
  have he := sum_homologyProjection_of_support N m (componentHomology N m p hN t x) T hs
  have him : (∑ d ∈ T, homologyProjection N m d.1 d.2.1 d.2.2
      (componentHomology N m p hN t x)) =
      ∑ i ∈ S, homologyProjection N m i.a.val i.b.val i.k.val
        (componentHomology N m p hN t x) := by
    apply Finset.sum_image
    intro i hi j hj hd
    apply ReversalFiber.eq_of_passiveIndex_degree_eq
    · exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
    · exact hd
  rw [him] at he
  rw [← he]
  dsimp only [S]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs with hit
  · rw [hit]
  · rfl

theorem fiberInclusion_projection_sum (N m p C w h : ℕ) (hN : 0 < N)
    (hC : m - 1 ≤ C) (hr : C < m + p) (x : reversalTargetPiece N m p w h) :
    ∑ i : ReversalFiber N m p C w h,
      fiberInclusion N m p C w h hN hr i (fiberProjection N m p C w h hN i x) = x := by
  apply Subtype.ext
  change (reversalTargetPiece N m p w h).subtype (∑ i : ReversalFiber N m p C w h, _) = x.val
  rw [map_sum]
  exact sum_include_component_projection N m p C w h hN hC hr x.property

/-- Finite homogeneous convolution for the full auxiliary reversal. -/
theorem homologyDimension_reversal (N m p C w h : ℕ) (hN : 0 < N)
    (hC : m - 1 ≤ C) (hr : C < m + p) :
    Auxiliary.homologyDimension N (N * (m + p) - m) (m + p) w h =
      ∑ i : ReversalFiber N m p C w h, homologyDimension N m i.a.val i.b.val i.k.val := by
  change Module.finrank ℚ (reversalTargetPiece N m p w h) =
    ∑ i : ReversalFiber N m p C w h, Module.finrank ℚ (reversalSourcePiece N m p C w h i)
  exact finrank_of_finiteDecomposition (V := reversalTargetPiece N m p w h)
    (ι := ReversalFiber N m p C w h) (fun i => ↥(reversalSourcePiece N m p C w h i))
    (fiberInclusion N m p C w h hN hr) (fiberProjection N m p C w h hN)
    (fiberProjection_inclusion N m p C w h hN hr)
    (fiberProjection_inclusion_ne N m p C w h hN hr)
    (fiberInclusion_projection_sum N m p C w h hN hC hr)

end TorusLinkHomology.HilbertSeries.GeneralReversal
