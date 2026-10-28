import TorusLinkHomology.HilbertSeries.Definitions
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Homogeneous chain spaces and their support bounds. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries
open CoordinateKoszul

/-- Unbounded indices of the rational chain basis. -/
abbrev ChainIndex (n : ℕ) := (Fin n →₀ ℕ) × Finset (Fin n)

/-- The three degrees of an unbounded basis index. -/
def monomialDegree (N : ℕ) {n : ℕ} (m : ChainIndex n) : ℕ × ℕ × ℕ :=
  ((∑ i : Fin n, m.1 i) + N * m.2.card,
    (∑ i : Fin n, i.val * m.1 i) + (∑ i ∈ m.2, i.val), m.2.card)

/-- Projection onto the basis vectors of a specified degree. -/
def homogeneousProjection (N n a b h : ℕ) : A n →ₗ[ℚ] A n := by
  classical
  exact (rationalChainBasis n).rationalDiagonal
    (fun m => if monomialDegree N m = (a, b, h) then 1 else 0)

@[simp] theorem homogeneousProjection_basis (N n a b h : ℕ) (m : ChainIndex n) :
    homogeneousProjection N n a b h (rationalChainBasis n m) =
      if monomialDegree N m = (a, b, h) then rationalChainBasis n m else 0 := by
  classical
  simp only [homogeneousProjection, Module.Basis.rationalDiagonal_basis]
  split_ifs <;> simp

@[simp] theorem repr_homogeneousProjection (N n a b h : ℕ) (x : A n)
    (m : ChainIndex n) :
    (rationalChainBasis n).repr (homogeneousProjection N n a b h x) m =
      if monomialDegree N m = (a, b, h) then (rationalChainBasis n).repr x m else 0 := by
  classical
  simp only [homogeneousProjection, Module.Basis.repr_rationalDiagonal]
  split_ifs <;> simp

theorem homogeneousProjection_idempotent (N n a b h : ℕ) (x : A n) :
    homogeneousProjection N n a b h (homogeneousProjection N n a b h x) =
      homogeneousProjection N n a b h x := by
  apply (rationalChainBasis n).repr.injective
  ext m
  classical
  simp only [repr_homogeneousProjection]
  split_ifs <;> rfl

@[simp] theorem monomialDegree_zero_iff (N n : ℕ) (m : ChainIndex n) :
    monomialDegree N m = (0, 0, 0) ↔ m = (0, ∅) := by
  constructor
  · intro hm
    have hh : m.2.card = 0 := congrArg (fun d => d.2.2) hm
    have ha : (∑ i : Fin n, m.1 i) + N * m.2.card = 0 := congrArg Prod.fst hm
    apply Prod.ext
    · ext i
      exact (Finset.sum_eq_zero_iff.mp (Nat.add_eq_zero_iff.mp ha).1) i (Finset.mem_univ i)
    · exact Finset.card_eq_zero.mp hh
  · rintro rfl; simp [monomialDegree]

theorem homogeneousProjection_origin (N n : ℕ) :
    homogeneousProjection N n 0 0 0 = scalarProjection n := by
  apply (rationalChainBasis n).ext
  intro m
  classical
  simp only [homogeneousProjection_basis, scalarProjection_basis, monomialDegree_zero_iff]
  split_ifs with hm
  · subst m; exact rationalChainBasis_zero n
  · rfl

/-- The bounded definition spans exactly the basis indices of the given degree. -/
theorem chainPiece_eq_span_degree (N n a b h : ℕ) :
    chainPiece N n a b h = Submodule.span ℚ
      ((rationalChainBasis n) '' {m : ChainIndex n | monomialDegree N m = (a, b, h)}) := by
  unfold chainPiece
  congr 1
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨(Finsupp.equivFunOnFinite.symm (fun i => (m.val.1 i).val), m.val.2), ?_, rfl⟩
    obtain ⟨ha, hb, hh⟩ := m.property
    exact Prod.ext ha (Prod.ext hb hh)
  · rintro ⟨m, hm, rfl⟩
    have ha : (∑ i : Fin n, m.1 i) + N * m.2.card = a := congrArg Prod.fst hm
    have hi (i : Fin n) : m.1 i < a + 1 := by
      have := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
        Nat.zero_le (m.1 j)) (Finset.mem_univ i)
      omega
    let mb : BoundedMonomial n a := (fun i => ⟨m.1 i, hi i⟩, m.2)
    have hmb : HasDegree N n a b h mb := by
      exact ⟨ha, congrArg (fun d => d.2.1) hm, congrArg (fun d => d.2.2) hm⟩
    refine ⟨⟨mb, hmb⟩, ?_⟩
    apply congrArg (rationalChainBasis n)
    apply Prod.ext
    · ext i
      simp [mb]
    · rfl

theorem mem_chainPiece_iff (N n a b h : ℕ) (x : A n) :
    x ∈ chainPiece N n a b h ↔ ∀ m ∈ ((rationalChainBasis n).repr x).support,
      monomialDegree N m = (a, b, h) := by
  rw [chainPiece_eq_span_degree, (rationalChainBasis n).mem_span_image]
  rfl

theorem homogeneousProjection_mem (N n a b h : ℕ) (x : A n) :
    homogeneousProjection N n a b h x ∈ chainPiece N n a b h := by
  classical
  rw [mem_chainPiece_iff]
  intro m hm
  by_contra hd
  simp [Finsupp.mem_support_iff, hd] at hm

theorem homogeneousProjection_eq_self {N n a b h : ℕ} {x : A n}
    (hx : x ∈ chainPiece N n a b h) : homogeneousProjection N n a b h x = x := by
  classical
  apply (rationalChainBasis n).repr.injective
  ext m
  rw [repr_homogeneousProjection]
  by_cases hm : m ∈ ((rationalChainBasis n).repr x).support
  · rw [if_pos ((mem_chainPiece_iff N n a b h x).mp hx m hm)]
  · have hz : (rationalChainBasis n).repr x m = 0 := Finsupp.notMem_support_iff.mp hm
    simp [hz]

/-- Only the degrees occurring in the finite basis expansion are needed. -/
theorem sum_homogeneousProjection (N n : ℕ) (x : A n) :
    ∑ d ∈ ((rationalChainBasis n).repr x).support.image (monomialDegree N),
      homogeneousProjection N n d.1 d.2.1 d.2.2 x = x := by
  classical
  apply (rationalChainBasis n).repr.injective
  ext m
  simp only [map_sum, Finsupp.finsetSum_apply, repr_homogeneousProjection, Prod.eta]
  by_cases hm : m ∈ ((rationalChainBasis n).repr x).support
  · have hd := Finset.mem_image_of_mem (monomialDegree N) hm
    simp only [Finset.sum_ite_eq, if_pos hd]
  · simp [Finsupp.notMem_support_iff.mp hm]

theorem HasDegree.exterior_bound {N n a b h : ℕ} {m : BoundedMonomial n a}
    (hm : HasDegree N n a b h m) : N * h ≤ a := by
  obtain ⟨ha, _, hh⟩ := hm
  calc
    N * h = N * m.2.card := congrArg (N * ·) hh.symm
    _ ≤ (∑ i : Fin n, (m.1 i).val) + N * m.2.card := Nat.le_add_left _ _
    _ = a := ha

theorem HasDegree.weight_bound {N n a b h : ℕ} (hN : 0 < N)
    {m : BoundedMonomial n a} (hm : HasDegree N n a b h m) : b ≤ (n - 1) * a := by
  obtain ⟨ha, hb, hh⟩ := hm
  have hp : (∑ i : Fin n, i.val * (m.1 i).val) ≤
      (n - 1) * ∑ i : Fin n, (m.1 i).val := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (by omega)
  have he : (∑ i ∈ m.2, i.val) ≤ (n - 1) * m.2.card := by
    calc
      _ ≤ ∑ _i ∈ m.2, (n - 1) := Finset.sum_le_sum fun i _ => by omega
      _ = _ := by simp [Nat.mul_comm]
  have hc : m.2.card ≤ N * m.2.card := by
    exact le_mul_of_one_le_left (Nat.zero_le _) hN
  calc
    b ≤ (n - 1) * ((∑ i : Fin n, (m.1 i).val) + m.2.card) := by
      rw [← hb, Nat.mul_add]; omega
    _ ≤ (n - 1) * a := Nat.mul_le_mul_left _ (by omega)

theorem chainPiece_eq_bot_of_no_degree (N n a b h : ℕ)
    (he : ∀ m : BoundedMonomial n a, ¬ HasDegree N n a b h m) :
    chainPiece N n a b h = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨m, rfl⟩
  exact (he m.val m.property).elim

theorem chainPiece_eq_bot_of_exterior_bound {N n a b h : ℕ} (ha : a < N * h) :
    chainPiece N n a b h = ⊥ := by
  apply chainPiece_eq_bot_of_no_degree
  intro m hm
  exact (not_le_of_gt ha) hm.exterior_bound

theorem chainPiece_eq_bot_of_weight_bound {N n a b h : ℕ} (hN : 0 < N)
    (hb : (n - 1) * a < b) : chainPiece N n a b h = ⊥ := by
  apply chainPiece_eq_bot_of_no_degree
  intro m hm
  exact (not_le_of_gt hb) (hm.weight_bound hN)

theorem cyclePiece_eq_bot_of_chainPiece_eq_bot {N n a b h : ℕ}
    (hc : chainPiece N n a b h = ⊥) : cyclePiece N n a b h = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change (x : A n) ∈ chainPiece N n a b h at hx
  rw [hc, Submodule.mem_bot] at hx
  exact Subtype.ext hx

theorem homologyPiece_eq_bot_of_chainPiece_eq_bot {N n a b h : ℕ}
    (hc : chainPiece N n a b h = ⊥) : homologyPiece N n a b h = ⊥ := by
  simp [homologyPiece, cyclePiece_eq_bot_of_chainPiece_eq_bot hc]

theorem homologyDimension_eq_zero_of_chainPiece_eq_bot {N n a b h : ℕ}
    (hc : chainPiece N n a b h = ⊥) : homologyDimension N n a b h = 0 := by
  simp [homologyDimension, homologyPiece_eq_bot_of_chainPiece_eq_bot hc]

theorem homologyDimension_eq_zero_of_exterior_bound {N n a b h : ℕ}
    (ha : a < N * h) : homologyDimension N n a b h = 0 :=
  homologyDimension_eq_zero_of_chainPiece_eq_bot (chainPiece_eq_bot_of_exterior_bound ha)

theorem homologyDimension_eq_zero_of_weight_bound {N n a b h : ℕ} (hN : 0 < N)
    (hb : (n - 1) * a < b) : homologyDimension N n a b h = 0 :=
  homologyDimension_eq_zero_of_chainPiece_eq_bot (chainPiece_eq_bot_of_weight_bound hN hb)

/-- Distinct bounded indices remain distinct in the rational chain basis. -/
theorem chainMonomial_linearIndependent (n a : ℕ) :
    LinearIndependent ℚ (chainMonomial n a) := by
  apply (rationalChainBasis n).linearIndependent.comp
    (fun m : BoundedMonomial n a =>
      (Finsupp.equivFunOnFinite.symm (fun i => (m.1 i).val), m.2))
  intro m m' he
  apply Prod.ext
  · funext i
    apply Fin.ext
    exact congrArg (fun x : ChainIndex n => x.1 i) he
  · exact congrArg (fun x : ChainIndex n => x.2) he

/-- Counting the homogeneous monomials computes the chain dimension. -/
theorem finrank_chainPiece (N n a b h : ℕ) :
    Module.finrank ℚ (chainPiece N n a b h) =
      Nat.card {m : BoundedMonomial n a // HasDegree N n a b h m} := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact finrank_span_eq_card ((chainMonomial_linearIndependent n a).comp
    Subtype.val Subtype.val_injective)

@[simp] theorem finrank_chainPiece_origin (N n : ℕ) :
    Module.finrank ℚ (chainPiece N n 0 0 0) = 1 := by
  rw [finrank_chainPiece]
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro x y
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact Fin.ext (by have hx := (x.val.1 i).isLt; have hy := (y.val.1 i).isLt; omega)
    · exact (Finset.card_eq_zero.mp x.property.2.2).trans
        (Finset.card_eq_zero.mp y.property.2.2).symm
  · exact ⟨⟨(fun _ => 0, ∅), by simp [HasDegree]⟩⟩

/-- Every polynomial index actually used by a monomial is bounded by its weight. -/
theorem HasDegree.polynomial_index_le {N n a b h : ℕ} {m : BoundedMonomial n a}
    (hm : HasDegree N n a b h m) {i : Fin n} (hi : (m.1 i).val ≠ 0) : i.val ≤ b := by
  have hs := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => Nat.zero_le (j.val * (m.1 j).val))
    (Finset.mem_univ i)
  have hp : i.val ≤ i.val * (m.1 i).val := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hi)
  have hw := hm.2.1
  omega

/-- Every exterior index actually used by a monomial is bounded by its weight. -/
theorem HasDegree.exterior_index_le {N n a b h : ℕ} {m : BoundedMonomial n a}
    (hm : HasDegree N n a b h m) {i : Fin n} (hi : i ∈ m.2) : i.val ≤ b := by
  have hs := Finset.single_le_sum (fun j (_ : j ∈ m.2) => Nat.zero_le j.val) hi
  have hw := hm.2.1
  omega

/-- Differential on a homogeneous chain space, with values in total cycles. -/
def chainDifferential (N n a b h : ℕ) :
    chainPiece N n a b h →ₗ[ℚ] (torusLinkDGA N n).cycles where
  toFun x := ⟨d N n x, d_squared N n x⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_rat_smul _ _ _)

/-- Homogeneous boundaries have primitives in the next chain degree. -/
def boundaryPiece (N n a b h : ℕ) : Submodule ℚ (torusLinkDGA N n).cycles :=
  LinearMap.range (chainDifferential N n a b (h + 1))

instance boundaryPiece_finiteDimensional (N n a b h : ℕ) :
    FiniteDimensional ℚ (boundaryPiece N n a b h) := by
  unfold boundaryPiece
  infer_instance

/-- The kernel on a homogeneous chain space is the existing homogeneous cycle space. -/
def chainDifferentialKerEquiv (N n a b h : ℕ) :
    LinearMap.ker (chainDifferential N n a b h) ≃ₗ[ℚ] cyclePiece N n a b h where
  toFun x := ⟨⟨x.val.val, congrArg Subtype.val x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, Subtype.ext x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Rank–nullity with the degree-zero case excluded by using a successor. -/
theorem finrank_chainPiece_succ (N n a b h : ℕ) :
    Module.finrank ℚ (chainPiece N n a b (h + 1)) =
      Module.finrank ℚ (cyclePiece N n a b (h + 1)) +
      Module.finrank ℚ (boundaryPiece N n a b h) := by
  have he := (chainDifferential N n a b (h + 1)).finrank_range_add_finrank_ker
  rw [(chainDifferentialKerEquiv N n a b (h + 1)).finrank_eq] at he
  exact he.symm.trans (Nat.add_comm _ _)

/-- The differential vanishes on exterior degree zero. -/
theorem d_eq_zero_of_mem_chainPiece_zero {N n a b : ℕ} {x : A n}
    (hx : x ∈ chainPiece N n a b 0) : d N n x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    have hm : m.val.2 = ∅ := Finset.card_eq_zero.mp m.property.2.2
    simp [chainMonomial, rationalChainBasis_apply, hm, d]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul r x hx ih => simp [map_rat_smul, ih]

/-- At degree zero there is no outgoing boundary term. -/
theorem finrank_chainPiece_zero (N n a b : ℕ) :
    Module.finrank ℚ (chainPiece N n a b 0) =
      Module.finrank ℚ (cyclePiece N n a b 0) := by
  have hz : chainDifferential N n a b 0 = 0 := by
    ext x
    exact d_eq_zero_of_mem_chainPiece_zero x.property
  have he := (chainDifferential N n a b 0).finrank_range_add_finrank_ker
  rw [(chainDifferentialKerEquiv N n a b 0).finrank_eq, hz,
    LinearMap.range_zero, finrank_bot, zero_add] at he
  exact he.symm

/-- Taking the class of a homogeneous cycle as a rational linear map. -/
def cycleClassMap (N n a b h : ℕ) : cyclePiece N n a b h →ₗ[ℚ] Homology N n :=
  ((torusLinkDGA N n).homologyClass.toLinearMap.restrictScalars ℚ).comp
    (cyclePiece N n a b h).subtype

theorem range_cycleClassMap (N n a b h : ℕ) :
    LinearMap.range (cycleClassMap N n a b h) = homologyPiece N n a b h := by
  exact LinearMap.range_comp _ _ |>.trans (by rw [Submodule.range_subtype]; rfl)

/-- Dimension additivity before identifying null classes with homogeneous boundaries. -/
theorem finrank_cyclePiece (N n a b h : ℕ) :
    Module.finrank ℚ (cyclePiece N n a b h) = homologyDimension N n a b h +
      Module.finrank ℚ (LinearMap.ker (cycleClassMap N n a b h)) := by
  have he := (cycleClassMap N n a b h).finrank_range_add_finrank_ker
  rw [range_cycleClassMap] at he
  exact he.symm

end TorusLinkHomology.HilbertSeries
