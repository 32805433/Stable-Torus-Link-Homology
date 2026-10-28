import TorusLinkHomology.HilbertSeries.GradedHomology
import TorusLinkHomology.HilbertSeries.Gordon

/-! The exponent-one case, including nonvanishing of the scalar class. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries
open CoordinateKoszul

/-- The scalar projection kills coordinate-Koszul boundaries. -/
theorem scalarProjection_d_one (n : ℕ) (x : A n) : scalarProjection n (d 1 n x) = 0 := by
  have hs : d 1 n (scalarProjection n x) = 0 := by simp [scalarProjection_apply, d]
  have he := coordinateHomotopy_identity n (d 1 n x)
  have hd := congrArg (d 1 n) (coordinateHomotopy_identity n x)
  simp only [map_add, map_sub, d_squared, zero_add, hs, sub_zero] at hd
  simp only [d_squared, map_zero, add_zero, hd] at he
  exact (sub_eq_self.mp he.symm)

/-- In positive tridegrees the contraction has no scalar term. -/
theorem scalarProjection_eq_zero_of_degree {N n a b h : ℕ} {x : A n}
    (hx : x ∈ chainPiece N n a b h) (habh : (a, b, h) ≠ (0, 0, 0)) :
    scalarProjection n x = 0 := by
  have hz : (rationalChainBasis n).repr x (0, ∅) = 0 := by
    by_contra he
    have hd := (mem_chainPiece_iff N n a b h x).mp hx (0, ∅)
      (Finsupp.mem_support_iff.mpr he)
    exact habh (hd.symm.trans (by simp [monomialDegree]))
  simp [scalarProjection_apply, hz]

/-- All non-scalar homogeneous homology pieces contract when N = 1. -/
theorem homologyDimension_one_of_nonzero {n a b h : ℕ}
    (habh : (a, b, h) ≠ (0, 0, 0)) : homologyDimension 1 n a b h = 0 := by
  have hp : homologyPiece 1 n a b h = ⊥ := by
    apply le_antisymm _ bot_le
    rintro x ⟨z, hz, rfl⟩
    change (torusLinkDGA 1 n).homologyClass z = 0
    apply (torusLinkDGA 1 n).homologyClass_eq_zero_iff z |>.mpr
    refine ⟨coordinateHomotopy n z, ?_⟩
    change (z : A n) ∈ chainPiece 1 n a b h at hz
    have he := coordinateHomotopy_identity n z
    have hd : d 1 n z = 0 := z.property
    rw [hd, map_zero, add_zero, scalarProjection_eq_zero_of_degree hz habh, sub_zero] at he
    exact he
  simp [homologyDimension, hp]

/-- The scalar homogeneous class survives the coordinate contraction. -/
@[simp] theorem homologyDimension_one_origin (n : ℕ) : homologyDimension 1 n 0 0 0 = 1 := by
  have hk : LinearMap.ker (cycleClassMap 1 n 0 0 0) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    change (torusLinkDGA 1 n).homologyClass x.val = 0 at hx
    obtain ⟨y, hy⟩ := (torusLinkDGA 1 n).homologyClass_eq_zero_iff x.val |>.mp hx
    have hs : scalarProjection n x.val.val = x.val.val := by
      rw [← homogeneousProjection_origin 1 n]
      exact homogeneousProjection_eq_self x.property
    have hx0 : x.val.val = 0 := by
      rw [← hs, ← hy]
      exact scalarProjection_d_one n y
    exact Subtype.ext (Subtype.ext hx0)
  have he := finrank_cyclePiece 1 n 0 0 0
  rw [hk, finrank_bot, add_zero, ← finrank_chainPiece_zero, finrank_chainPiece_origin] at he
  exact he.symm

theorem homologyDimension_one (n a b h : ℕ) :
    homologyDimension 1 n a b h = if a = 0 ∧ b = 0 ∧ h = 0 then 1 else 0 := by
  split_ifs with hz
  · obtain ⟨rfl, rfl, rfl⟩ := hz; exact homologyDimension_one_origin n
  · apply homologyDimension_one_of_nonzero
    intro he
    exact hz ⟨congrArg Prod.fst he, congrArg (fun t => t.2.1) he,
      congrArg (fun t => t.2.2) he⟩

/-- The stable coefficient formula for N = 1 holds even at length zero. -/
theorem stable_homology_coefficient_one (k b h n : ℕ) :
    (homologyDimension 1 n (k + 1 * h) b h : ℚ) =
      MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b)
        (fermionicCoefficient 1 k) := by
  classical
  rw [homologyDimension_one, fermionicCoefficient_rank_one]
  by_cases hk : k = 0
  · subst k
    simp only [↓reduceIte, MvPowerSeries.coeff_one, one_mul, zero_add]
    have he : Finsupp.single (0 : Fin 2) h + Finsupp.single 1 b = 0 ↔ h = 0 ∧ b = 0 := by
      constructor
      · intro he
        have hh := congrArg (fun e : Fin 2 →₀ ℕ => e 0) he
        have hb := congrArg (fun e : Fin 2 →₀ ℕ => e 1) he
        simpa using And.intro hh hb
      · rintro ⟨rfl, rfl⟩; simp
    simp [he, and_comm, and_left_comm]
  · simp [hk, Nat.add_eq_zero_iff]

end TorusLinkHomology.HilbertSeries
