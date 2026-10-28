import TorusLinkHomology.HilbertSeries.Stabilization
import TorusLinkHomology.HilbertSeries.GradedDifferential

/-! Transport of homogeneous cycles and boundaries under extension of indices. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries
open CoordinateKoszul

theorem chainBasis_eq_sort_prod (n : ℕ) (s : Finset (Fin n)) :
    chainBasis n s = (s.sort.map (xi n)).prod := by
  rw [chainBasis, ExteriorAlgebra.basis_apply_ofCard _ rfl]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, Function.comp_apply]
  congr 1
  change List.ofFn (fun i : Fin s.card => xi n (s.orderEmbOfFin rfl i)) = _
  rw [List.ofFn_comp']
  congr 1
  rw [List.ofFn_eq_map, Finset.listMap_orderEmbOfFin_finRange]

@[simp] theorem extendChains_chainBasis (n : ℕ) (s : Finset (Fin n)) :
    extendChains n (chainBasis n s) = chainBasis (n + 1) (s.map Fin.castSuccEmb) := by
  classical
  rw [chainBasis_eq_sort_prod, chainBasis_eq_sort_prod, map_list_prod, List.map_map]
  have hs : s.sort.map (Fin.castSuccEmb (n := n)) = (s.map Fin.castSuccEmb).sort :=
    Finset.map_sort _ _ _ _ (by intro a ha b hb; exact Iff.rfl)
  rw [← hs, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact extendChains_xi n i

@[simp] theorem extendChains_chainMonomial (n a : ℕ) (m : BoundedMonomial n a) :
    extendChains n (chainMonomial n a m) =
      chainMonomial (n + 1) a (extendBoundedMonomial n a m) := by
  classical
  simp only [chainMonomial, rationalChainBasis_apply, extendChains_smul,
    extendChains_chainBasis, extendBoundedMonomial]
  congr 1
  change MvPolynomial.rename Fin.castSucc _ = _
  rw [MvPolynomial.rename_monomial]
  apply congrArg (fun d : Fin (n + 1) →₀ ℕ => MvPolynomial.monomial d (1 : ℚ))
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Finsupp.mapDomain_of_notMem_range]
    · simp
    · rintro ⟨j, hj⟩
      exact Fin.castSucc_ne_last j hj
  · rw [Finsupp.mapDomain_apply (Fin.castSucc_injective n)]
    simp

@[simp] theorem coe_homogeneousChainBasis (N n a b h : ℕ)
    (m : {m : BoundedMonomial n a // HasDegree N n a b h m}) :
    (homogeneousChainBasis N n a b h m).val = chainMonomial n a m.val :=
  Module.Basis.coe_span_apply _ _

/-- The basis equivalence is exactly the inclusion of coefficient Koszul chains. -/
theorem coe_chainPieceEquivSucc (N n a b h : ℕ) (hb : b < n)
    (x : chainPiece N n a b h) :
    (chainPieceEquivSucc N n a b h hb x).val = extendChains n x.val := by
  have he : (chainPiece N (n + 1) a b h).subtype.comp
      (chainPieceEquivSucc N n a b h hb).toLinearMap =
      (extendChains n).toAddMonoidHom.toRatLinearMap.comp (chainPiece N n a b h).subtype := by
    apply (homogeneousChainBasis N n a b h).ext
    intro m
    change (chainPieceEquivSucc N n a b h hb (homogeneousChainBasis N n a b h m)).val =
      extendChains n (homogeneousChainBasis N n a b h m).val
    rw [chainPieceEquivSucc_basis, coe_homogeneousChainBasis, coe_homogeneousChainBasis,
      extendChains_chainMonomial]
    rfl
  exact LinearMap.congr_fun he x

/-- A chain equivalence preserving and reflecting cycles induces an equivalence
of the already defined homogeneous cycle spaces. -/
def cyclePieceEquivOfChainEquiv {N n m a b h : ℕ}
    (e : chainPiece N n a b h ≃ₗ[ℚ] chainPiece N m a b h)
    (he : ∀ x : chainPiece N n a b h, d N m (e x).val = 0 ↔ d N n x.val = 0) :
    cyclePiece N n a b h ≃ₗ[ℚ] cyclePiece N m a b h where
  toFun z := ⟨⟨(e ⟨z.val.val, z.property⟩).val,
    (he ⟨z.val.val, z.property⟩).mpr z.val.property⟩, (e ⟨z.val.val, z.property⟩).property⟩
  invFun z := ⟨⟨(e.symm ⟨z.val.val, z.property⟩).val,
    (he (e.symm ⟨z.val.val, z.property⟩)).mp (by
      rw [e.apply_symm_apply]; exact z.val.property)⟩,
    (e.symm ⟨z.val.val, z.property⟩).property⟩
  left_inv z := by
    apply Subtype.ext; apply Subtype.ext
    change (e.symm (e ⟨z.val.val, z.property⟩)).val = z.val.val
    rw [e.symm_apply_apply]
  right_inv z := by
    apply Subtype.ext; apply Subtype.ext
    change (e (e.symm ⟨z.val.val, z.property⟩)).val = z.val.val
    rw [e.apply_symm_apply]
  map_add' x y := by
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun z : chainPiece N m a b h => z.val)
      (e.map_add ⟨x.val.val, x.property⟩ ⟨y.val.val, y.property⟩)
  map_smul' r x := by
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun z : chainPiece N m a b h => z.val)
      (e.map_smul r ⟨x.val.val, x.property⟩)

/-- Cycles stabilize in each homogeneous piece as soon as n exceeds its weight. -/
def cyclePieceEquivSucc (N n a b h : ℕ) (hb : b < n) :
    cyclePiece N n a b h ≃ₗ[ℚ] cyclePiece N (n + 1) a b h :=
  cyclePieceEquivOfChainEquiv (chainPieceEquivSucc N n a b h hb) (by
    intro x
    rw [coe_chainPieceEquivSucc, extendChains_d]
    exact (extendChains_injective n).eq_iff' (map_zero _))

theorem finrank_cyclePiece_succ_stable (N n a b h : ℕ) (hb : b < n) :
    Module.finrank ℚ (cyclePiece N n a b h) =
      Module.finrank ℚ (cyclePiece N (n + 1) a b h) :=
  (cyclePieceEquivSucc N n a b h hb).finrank_eq

/-- Boundary dimensions stabilize by rank–nullity on the next chain space. -/
theorem finrank_boundaryPiece_succ_stable (N n a b h : ℕ) (hb : b < n) :
    Module.finrank ℚ (boundaryPiece N n a b h) =
      Module.finrank ℚ (boundaryPiece N (n + 1) a b h) := by
  have hc := finrank_chainPiece_succ_stable N n a b (h + 1) hb
  rw [finrank_chainPiece_succ, finrank_chainPiece_succ,
    finrank_cyclePiece_succ_stable N n a b (h + 1) hb] at hc
  exact Nat.add_left_cancel hc

/-- The actual homology dimensions stabilize, with no positivity assumption on N. -/
theorem homologyDimension_succ_stable (N n a b h : ℕ) (hb : b < n) :
    homologyDimension N n a b h = homologyDimension N (n + 1) a b h := by
  have hc := finrank_cyclePiece_succ_stable N n a b h hb
  rw [finrank_cyclePiece_eq_homology_add_boundary,
    finrank_cyclePiece_eq_homology_add_boundary,
    finrank_boundaryPiece_succ_stable N n a b h hb] at hc
  exact Nat.add_right_cancel hc

/-- Every finite stage n > b computes the same coefficient as stage b + 1. -/
theorem homologyDimension_stable (N n a b h : ℕ) (hb : b < n) :
    homologyDimension N n a b h = homologyDimension N (b + 1) a b h := by
  induction n, Nat.succ_le_of_lt hb using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [← homologyDimension_succ_stable N n a b h (by omega)]
    exact ih (by omega)

end TorusLinkHomology.HilbertSeries
