import TorusLinkHomology.Generation.ShortRangeCycles

/-!
# Explicit ordered expansions in the named cycles

The adapted coordinate witness becomes a literal finite sum of ordered
products. Exterior factors are multiplied in the increasing order recorded by
`Finset.sort`; no commutative product on the exterior algebra is used.
-/

noncomputable section

open scoped BigOperators

namespace ExteriorAlgebra

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LinearOrder ι]

/-- The standard exterior basis is the increasing ordered product of its
degree-one factors. -/
theorem basis_eq_sortedProduct (b : Module.Basis ι R M) (s : Finset ι) :
    b.ExteriorAlgebra s = (s.sort.map (fun i => ExteriorAlgebra.ι R (b i))).prod := by
  rw [basis_apply]
  simp only [ιMulti_family, ιMulti_apply, List.ofFn_eq_map]
  change ((List.finRange s.card).map
    ((fun i => ExteriorAlgebra.ι R (b i)) ∘ s.orderEmbOfFin rfl)).prod = _
  rw [← List.map_map, Finset.listMap_orderEmbOfFin_finRange]

end ExteriorAlgebra

namespace TorusLinkHomology.Generation

section Projection

variable {R ι : Type*} [CommRing R] [Fintype ι] [LinearOrder ι]

/-- Erasing one generator deletes exactly the basis monomials containing it. -/
theorem map_eraseCoordinate_basis (r : ι) (s : Finset ι) :
    ExteriorAlgebra.map (eraseCoordinate r) ((Pi.basisFun R ι).ExteriorAlgebra s) =
      if r ∈ s then 0 else (Pi.basisFun R ι).ExteriorAlgebra s := by
  simp only [ExteriorAlgebra.basis_eq_sortedProduct, map_list_prod, List.map_map]
  by_cases hr : r ∈ s
  · rw [if_pos hr]
    apply List.prod_eq_zero
    apply List.mem_map.mpr
    refine ⟨r, by simpa using hr, ?_⟩
    simp only [Function.comp_apply, ExteriorAlgebra.map_apply_ι,
      eraseCoordinate_basis, ↓reduceIte, map_zero]
  · rw [if_neg hr]
    congr 1
    apply List.map_congr_left
    intro i hi
    have himem : i ∈ s := by simpa using hi
    have hir : i ≠ r := fun h => hr (h ▸ himem)
    simp only [Function.comp_apply, ExteriorAlgebra.map_apply_ι,
      eraseCoordinate_basis, if_neg hir]

/-- The coordinate formula for the auxiliary-generator projection. -/
theorem repr_map_eraseCoordinate (r : ι) (w : ExteriorAlgebra R (ι → R)) (s : Finset ι) :
    (Pi.basisFun R ι).ExteriorAlgebra.repr (ExteriorAlgebra.map (eraseCoordinate r) w) s =
      if r ∈ s then 0 else (Pi.basisFun R ι).ExteriorAlgebra.repr w s := by
  classical
  conv_lhs => rw [← (Pi.basisFun R ι).ExteriorAlgebra.sum_repr w]
  simp only [map_sum, map_smul, map_eraseCoordinate_basis]
  by_cases hr : r ∈ s <;>
    simp [apply_ite, ite_apply, Module.Basis.repr_self, Finsupp.single_apply, hr]

/-- A vector fixed by erasing a coordinate has no monomial using it. -/
theorem repr_eq_zero_of_eraseCoordinate_fixed (r : ι)
    (w : ExteriorAlgebra R (ι → R)) (hw : ExteriorAlgebra.map (eraseCoordinate r) w = w)
    (s : Finset ι) (hs : r ∈ s) : (Pi.basisFun R ι).ExteriorAlgebra.repr w s = 0 := by
  have h := congrArg (fun z => (Pi.basisFun R ι).ExteriorAlgebra.repr z s) hw
  rw [repr_map_eraseCoordinate, if_pos hs] at h
  exact h.symm

end Projection

/-- The unused named cycle at index zero is zero. -/
theorem mu_zero_index (N n : ℕ) : mu N n 0 = 0 := by
  unfold mu
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with h
  · have hi : i.val = 0 := by omega
    have hj : j.val = 0 := by omega
    simp [hi, hj]
  · rfl

/-- The cycle-substitution map sends every standard basis generator to the
named cycle with the same positive index (and sends index zero to zero). -/
theorem piMuMap_iota_basis (N a : ℕ) (j : Fin (a + 1)) :
    piMuMap N a (ExteriorAlgebra.ι (R (a + 1))
      (Pi.basisFun (R (a + 1)) (Fin (a + 1)) j)) = mu N (a + 1) j.val := by
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [piMuMap_iota_zero, Fin.val_zero, mu_zero_index]
  · exact piMuMap_iota_succ N a j

/-- The factors are the μ's in increasing order of their indices. -/
def orderedMuProduct (N a : ℕ) (s : Finset (Fin (a + 1))) : A (a + 1) :=
  (s.sort.map (fun j => mu N (a + 1) j.val)).prod

@[simp] theorem orderedMuProduct_empty (N a : ℕ) : orderedMuProduct N a ∅ = 1 := by
  simp [orderedMuProduct]

@[simp] theorem orderedMuProduct_singleton (N a : ℕ) (j : Fin (a + 1)) :
    orderedMuProduct N a {j} = mu N (a + 1) j.val := by
  simp [orderedMuProduct]

/-- Substitution turns a standard exterior monomial into its literal ordered
product of named cycles. -/
theorem piMuMap_basis (N a : ℕ) (s : Finset (Fin (a + 1))) :
    piMuMap N a ((Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra s) =
      orderedMuProduct N a s := by
  rw [ExteriorAlgebra.basis_eq_sortedProduct, map_list_prod]
  simp only [List.map_map, Function.comp_def, piMuMap_iota_basis, orderedMuProduct]

/-- Expand an arbitrary adapted-coordinate vector under cycle substitution. -/
theorem piMuMap_eq_sum_orderedMuProduct (N a : ℕ) (w : PiCoordinates.PiA (a + 1)) :
    piMuMap N a w = ∑ s : Finset (Fin (a + 1)),
      ((Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr w s) •
        orderedMuProduct N a s := by
  conv_lhs => rw [← (Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.sum_repr w]
  simp only [map_sum, map_smul, piMuMap_basis]

/-- Recover the cycle-substitution value from an adapted coordinate witness. -/
theorem piMuMap_eq_of_coordinates (N a : ℕ) {x : A (a + 1)}
    {w : PiCoordinates.PiA (a + 1)}
    (hw : ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin' w = PiCoordinates.toPi (a + 1) x)
    (hp : ExteriorAlgebra.map (eraseCoordinate 0) w = w) : piMuMap N a w = x := by
  change (PiCoordinates.toPi (a + 1)).symm
    (ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin'
      (ExteriorAlgebra.map (eraseCoordinate 0) w)) = x
  rw [hp, hw, AlgEquiv.symm_apply_apply]

/-- A literal finite polynomial identity in increasing ordered μ-products.
Only subsets of the positive generator indices contribute. -/
theorem eq_sum_orderedMuProduct_of_coordinates (N a : ℕ) {x : A (a + 1)}
    {w : PiCoordinates.PiA (a + 1)}
    (hw : ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin' w = PiCoordinates.toPi (a + 1) x)
    (hp : ExteriorAlgebra.map (eraseCoordinate 0) w = w) :
    x = ∑ s ∈ Finset.univ.filter (fun s : Finset (Fin (a + 1)) => 0 ∉ s),
      ((Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr w s) •
        orderedMuProduct N a s := by
  rw [← piMuMap_eq_of_coordinates N a hw hp, piMuMap_eq_sum_orderedMuProduct,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : (0 : Fin (a + 1)) ∈ s
  · rw [repr_eq_zero_of_eraseCoordinate_fixed 0 w hp s hs]
    simp [hs]
  · simp [hs]

/-- For a homogeneous coordinate witness, the exact identity uses only
subsets of the prescribed cardinality. -/
theorem eq_sum_orderedMuProduct_card_of_coordinates (N a q : ℕ) {x : A (a + 1)}
    {w : PiCoordinates.PiA (a + 1)}
    (hw : ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin' w = PiCoordinates.toPi (a + 1) x)
    (hp : ExteriorAlgebra.map (eraseCoordinate 0) w = w)
    (hq : ∀ s : Finset (Fin (a + 1)), s.card ≠ q →
      ((Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr w s) = 0) :
    x = ∑ s ∈ Finset.univ.filter (fun s : Finset (Fin (a + 1)) => 0 ∉ s ∧ s.card = q),
      ((Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr w s) •
        orderedMuProduct N a s := by
  rw [← piMuMap_eq_of_coordinates N a hw hp, piMuMap_eq_sum_orderedMuProduct,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : (0 : Fin (a + 1)) ∈ s
  · rw [repr_eq_zero_of_eraseCoordinate_fixed 0 w hp s hs]
    simp [hs]
  · by_cases hcard : s.card = q
    · simp [hs, hcard]
    · rw [hq s hcard]
      simp

/-- The exterior vector with a specified finite family of standard coordinates. -/
def muCoordinateVector (a : ℕ) (c : Finset (Fin (a + 1)) → R (a + 1)) :
    PiCoordinates.PiA (a + 1) :=
  ∑ s : Finset (Fin (a + 1)),
    c s • (Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra s

@[simp] theorem repr_muCoordinateVector (a : ℕ)
    (c : Finset (Fin (a + 1)) → R (a + 1)) (s : Finset (Fin (a + 1))) :
    (Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr
      (muCoordinateVector a c) s = c s := by
  simp [muCoordinateVector, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- Coefficient support away from zero is equivalent to the needed projection
condition on the reconstructed vector. -/
theorem eraseCoordinate_muCoordinateVector (a : ℕ)
    (c : Finset (Fin (a + 1)) → R (a + 1))
    (hc : ∀ s, (0 : Fin (a + 1)) ∈ s → c s = 0) :
    ExteriorAlgebra.map (eraseCoordinate 0) (muCoordinateVector a c) =
      muCoordinateVector a c := by
  apply (Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr.injective
  ext s
  rw [repr_map_eraseCoordinate, repr_muCoordinateVector]
  by_cases hs : (0 : Fin (a + 1)) ∈ s
  · simp [hs, hc s hs]
  · simp [hs]

/-- Cycle substitution is injective on vectors without the auxiliary exterior
coordinate. This holds at every length and exponent. -/
theorem piMuMap_injective_of_fixed (N a : ℕ) {v w : PiCoordinates.PiA (a + 1)}
    (hv : ExteriorAlgebra.map (eraseCoordinate 0) v = v)
    (hw : ExteriorAlgebra.map (eraseCoordinate 0) w = w)
    (h : piMuMap N a v = piMuMap N a w) : v = w := by
  apply muAdjoinedMatrix_zero_map_injective N a
  apply (PiCoordinates.toPi (a + 1)).symm.injective
  change (PiCoordinates.toPi (a + 1)).symm
      (ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin'
        (ExteriorAlgebra.map (eraseCoordinate 0) v)) =
    (PiCoordinates.toPi (a + 1)).symm
      (ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin'
        (ExteriorAlgebra.map (eraseCoordinate 0) w)) at h
  simpa only [hv, hw] using h

/-- Uniqueness of the literal ordered μ expansion. The zero-containing
coordinates are required to vanish because those products are themselves zero.
No homology quotient or rational-function coefficients occur here. -/
theorem orderedMuProduct_coefficients_unique (N a : ℕ)
    (c d : Finset (Fin (a + 1)) → R (a + 1))
    (hc : ∀ s, (0 : Fin (a + 1)) ∈ s → c s = 0)
    (hd : ∀ s, (0 : Fin (a + 1)) ∈ s → d s = 0)
    (h : (∑ s : Finset (Fin (a + 1)), c s • orderedMuProduct N a s) =
      ∑ s : Finset (Fin (a + 1)), d s • orderedMuProduct N a s) : c = d := by
  have heq : muCoordinateVector a c = muCoordinateVector a d := by
    apply piMuMap_injective_of_fixed N a
      (eraseCoordinate_muCoordinateVector a c hc) (eraseCoordinate_muCoordinateVector a d hd)
    simpa only [piMuMap_eq_sum_orderedMuProduct, repr_muCoordinateVector] using h
  funext s
  have hs := congrArg
    (fun w => (Pi.basisFun (R (a + 1)) (Fin (a + 1))).ExteriorAlgebra.repr w s) heq
  simpa only [repr_muCoordinateVector] using hs

end TorusLinkHomology.Generation
