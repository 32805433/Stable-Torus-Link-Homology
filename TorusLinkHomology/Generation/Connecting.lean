import TorusLinkHomology.Generation.ComparisonProjection

/-! # Connecting classes through explicit representatives

The quotient complex has a sign change in its differential. Retaining lifts
in the definition makes the signs and the independence of choices explicit,
without requiring a long exact sequence on homology.
-/

noncomputable section

namespace TorusLinkHomology.CoefficientComplex

/-- A representative of the connecting class of `a`, witnessed by a lift
to the middle complex. Offsets are written `ell+1` to avoid subtraction. -/
def ConnectingRepresentative (N r ell : ℕ) (a : A r) (z : A (r + 1)) : Prop :=
  ∃ w : A (r + 1), p r w = a ∧
    J N (r + 1) (ell + 1) z = d N (r + 1) ell w

theorem connectingRepresentative_exists (N r ell : ℕ)
    (hm : ell + 1 < N * (r + 1)) (a : A r) (ha : d N r (ell + 1) a = 0) :
    ∃ z, ConnectingRepresentative N r ell a z := by
  obtain ⟨z, _, hz⟩ := connecting_representative N r ell hm a ha
  exact ⟨z, xi (r + 1) 0 * includeCommon r a, p_lift r a, hz⟩

/-- Every connecting representative is a cycle. -/
theorem ConnectingRepresentative.is_cycle {N r ell : ℕ}
    (hm : ell + 1 < N * (r + 1)) {a : A r} {z : A (r + 1)}
    (hz : ConnectingRepresentative N r ell a z) : d N (r + 1) (ell + 1) z = 0 := by
  obtain ⟨w, _, hw⟩ := hz
  apply J_injective N r ell hm
  rw [← d_J, Nat.add_sub_cancel_right, hw, d_squared, map_zero]

/-- Subtracting two lift diagrams subtracts their connecting representatives. -/
theorem ConnectingRepresentative.sub {N r ell : ℕ} {a b : A r} {z t : A (r + 1)}
    (hz : ConnectingRepresentative N r ell a z)
    (ht : ConnectingRepresentative N r ell b t) :
    ConnectingRepresentative N r ell (a - b) (z - t) := by
  obtain ⟨w, hw, hzw⟩ := hz
  obtain ⟨v, hv, htv⟩ := ht
  refine ⟨w - v, ?_, ?_⟩
  · change dropFirst r (CliffordAlgebra.contractLeft (Q := 0)
      (firstCoordinate r) (w - v)) = _
    rw [map_sub, map_sub]
    change p r w - p r v = a - b
    rw [hw, hv]
  · rw [map_sub, map_sub, hzw, htv]

/-- If the source class is zero as a chain, its connecting representative
is already a boundary. -/
theorem ConnectingRepresentative.boundary_of_source_zero {N r ell : ℕ}
    (hm : ell + 1 < N * (r + 1)) {z : A (r + 1)}
    (hz : ConnectingRepresentative N r ell 0 z) :
    ∃ c, z = d N (r + 1) (ell + 1) c := by
  obtain ⟨w, hw, hzw⟩ := hz
  obtain ⟨c, hc⟩ := (p_eq_zero_iff N r ell hm w).mp hw
  refine ⟨c, J_injective N r ell hm ?_⟩
  rw [← d_J, Nat.add_sub_cancel_right, hc, hzw]

/-- Two choices of lifts give the same connecting class modulo boundaries. -/
theorem ConnectingRepresentative.eq_mod_boundary {N r ell : ℕ}
    (hm : ell + 1 < N * (r + 1)) {a : A r} {z t : A (r + 1)}
    (hz : ConnectingRepresentative N r ell a z)
    (ht : ConnectingRepresentative N r ell a t) :
    ∃ c, z = t + d N (r + 1) (ell + 1) c := by
  have hzt := hz.sub ht
  rw [sub_self] at hzt
  obtain ⟨c, hc⟩ := hzt.boundary_of_source_zero hm
  exact ⟨c, by rw [← hc]; abel⟩

/-- A boundary in the quotient has zero connecting class. The negative
differential of a lift is the lift required by the shifted differential. -/
theorem connectingRepresentative_boundary_zero (N r ell : ℕ) (q : A r) :
    ConnectingRepresentative N r ell (d N r (ell + 1) q) 0 := by
  obtain ⟨v, hv⟩ := p_surjective r q
  refine ⟨-d N (r + 1) ell v, ?_, ?_⟩
  · change dropFirst r (CliffordAlgebra.contractLeft (Q := 0)
      (firstCoordinate r) (-d N (r + 1) ell v)) = _
    rw [map_neg, map_neg]
    change -p r (d N (r + 1) ell v) = _
    rw [p_d, hv, neg_neg]
  · rw [map_zero, map_neg, d_squared, neg_zero]

theorem ConnectingRepresentative.boundary_of_source_boundary {N r ell : ℕ}
    (hm : ell + 1 < N * (r + 1)) {q : A r} {z : A (r + 1)}
    (hz : ConnectingRepresentative N r ell (d N r (ell + 1) q) z) :
    ∃ c, z = d N (r + 1) (ell + 1) c := by
  simpa only [zero_add] using
    hz.eq_mod_boundary hm (connectingRepresentative_boundary_zero N r ell q)

/-- The connecting map satisfies the projection formula, with the reduced
new cycle on the right and with no extra sign. -/
theorem ConnectingRepresentative.mul_cycle {N r ell : ℕ} {a : A r}
    {z b : A (r + 1)} (hz : ConnectingRepresentative N r ell a z)
    (hb : d N (r + 1) (ell + 1) b = 0) :
    ConnectingRepresentative N r ell (a * rhoSucc N r (ell + 1) b) (z * b) := by
  obtain ⟨w, hw, hzw⟩ := hz
  refine ⟨w * J N (r + 1) (ell + 1) b, ?_, ?_⟩
  · rw [p_mul_J, hw]
  · rw [map_mul, hzw]
    have hb' : d N (r + 1) ell (J N (r + 1) (ell + 1) b) = 0 := by
      simpa only [Nat.add_sub_cancel_right] using J_cycle N (r + 1) (ell + 1) hb
    exact ((dga N (r + 1) ell).d_mul_of_cycle hb' w).symm

/-- Exactness at new homology, expressed using cycle and boundary witnesses. -/
theorem exists_connectingRepresentative_iff (N r ell : ℕ) (z : A (r + 1)) :
    (∃ a : A r, d N r (ell + 1) a = 0 ∧ ConnectingRepresentative N r ell a z) ↔
      ∃ w : A (r + 1), J N (r + 1) (ell + 1) z = d N (r + 1) ell w := by
  constructor
  · rintro ⟨a, _, w, _, hw⟩
    exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    refine ⟨p r w, ?_, w, rfl, hw⟩
    have h := congrArg (p r) hw
    rw [p_J, p_d] at h
    exact neg_eq_zero.mp h.symm

end TorusLinkHomology.CoefficientComplex
