import TorusLinkHomology.HilbertSeries.Reversal
import TorusLinkHomology.HilbertSeries.StabilizationHomology
import Mathlib.Data.Finset.Sum
import Mathlib.LinearAlgebra.Finsupp.SumProd

/-! A decomposition into passive monomials and copies of the active chain space.
The polynomial block is ordered passive/active, while the exterior block is
ordered active/passive. Reversing the active basis removes exterior-order signs
from the block inclusion. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries.GeneralReversal
open CoordinateKoszul

/-- Coefficient reversal is also an equivalence of rational chain spaces. -/
def reverseRationalEquiv (m : ℕ) : A m ≃ₗ[ℚ] A m where
  toFun := TorusLinkHomology.Reversal.reverseChains m
  invFun := TorusLinkHomology.Reversal.reverseChains m
  left_inv := TorusLinkHomology.Reversal.reverseChains_involutive m
  right_inv := TorusLinkHomology.Reversal.reverseChains_involutive m
  map_add' := map_add _
  map_smul' := map_rat_smul _

/-- Use the reversed rational monomial basis on the active factor. -/
def activeBasis (m : ℕ) : Module.Basis (ChainIndex m) ℚ (A m) :=
  (rationalChainBasis m).map (reverseRationalEquiv m)

/-- Split polynomial exponents into the high active block and the low passive block. -/
def splitPolynomialIndex (m p : ℕ) :
    (Fin (m + p) →₀ ℕ) ≃ (Fin m →₀ ℕ) × (Fin p →₀ ℕ) :=
  ((Finsupp.domCongr ((finCongr (Nat.add_comm m p)).trans finSumFinEquiv.symm)).toEquiv.trans
    Finsupp.sumFinsuppEquivProdFinsupp).trans (Equiv.prodComm _ _)

/-- Split exterior indices into the low active block and the high passive block. -/
def splitExteriorIndex (m p : ℕ) :
    Finset (Fin (m + p)) ≃ Finset (Fin m) × Finset (Fin p) :=
  (Equiv.finsetCongr finSumFinEquiv.symm).trans Finset.sumEquiv.toEquiv

/-- Each auxiliary monomial has unique passive and active indices. -/
def splitChainIndex (m p : ℕ) :
    ChainIndex (m + p) ≃ ChainIndex p × ChainIndex m :=
  ((splitPolynomialIndex m p).prodCongr (splitExteriorIndex m p)).trans
    ((Equiv.prodProdProdComm _ _ _ _).trans (Equiv.prodComm _ _))

/-- The chain vector space is a finitely supported family of active chain spaces,
indexed by passive polynomial/exterior monomials. -/
def decomposeChains (m p : ℕ) : A (m + p) ≃ₗ[ℚ] (ChainIndex p →₀ A m) :=
  (rationalChainBasis (m + p)).repr ≪≫ₗ
    Finsupp.domLCongr (splitChainIndex m p) ≪≫ₗ
      Finsupp.curryLinearEquiv ℚ ≪≫ₗ
        Finsupp.mapRange.linearEquiv (activeBasis m).repr.symm

@[simp] theorem decomposeChains_basis (m p : ℕ) (q : ChainIndex (m + p)) :
    decomposeChains m p (rationalChainBasis (m + p) q) =
      Finsupp.single ((splitChainIndex m p q).1)
        (activeBasis m (splitChainIndex m p q).2) := by
  change Finsupp.mapRange (activeBasis m).repr.symm (map_zero _)
    (Finsupp.equivMapDomain (splitChainIndex m p)
      ((rationalChainBasis (m + p)).repr (rationalChainBasis (m + p) q))).curry = _
  rw [Module.Basis.repr_self, Finsupp.equivMapDomain_single, Finsupp.curry_single,
    Finsupp.mapRange_single, Module.Basis.repr_symm_single, one_smul]

/-- Polynomial indices in the high active block. -/
def highPolynomialIndex (m p : ℕ) : Fin m ↪ Fin (m + p) where
  toFun i := ⟨p + i.val, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

/-- Polynomial indices in the low passive block. -/
def lowPolynomialIndex (m p : ℕ) : Fin p ↪ Fin (m + p) :=
  Fin.castLEEmb (Nat.le_add_left p m)

/-- The block inclusion obtained after reversing the active source. -/
def blockChains (m p : ℕ) : A m →+* A (m + p) :=
  (activeChains m (m + p) (Nat.le_add_right m p)).comp
    (TorusLinkHomology.Reversal.reverseChains m)

@[simp] theorem blockChains_xi (m p : ℕ) (i : Fin m) :
    blockChains m p (xi m i) = xi (m + p) (Fin.castAdd p i) := by
  simp only [blockChains, RingHom.comp_apply, TorusLinkHomology.Reversal.reverseChains_xi]
  change activeChains m (m + p) _ (xi m i.rev) = _
  rw [activeChains_xi, Fin.rev_rev]
  rfl

@[simp] theorem blockCoefficients_u (m p : ℕ) (i : Fin m) :
    activeCoefficients m (m + p) (Nat.le_add_right m p)
      (TorusLinkHomology.Reversal.reverseCoefficients m (u m i)) =
      u (m + p) (highPolynomialIndex m p i) := by
  rw [TorusLinkHomology.Reversal.reverseCoefficients_u]
  change activeCoefficients m (m + p) _ (u m i.rev) = _
  rw [activeCoefficients_u]
  congr 1
  apply Fin.ext
  change m + p - (m - (i.val + 1) + 1) = p + i.val
  have := i.isLt
  omega

/-- Passive polynomial and exterior monomials. -/
def passiveMonomial (m p : ℕ) (t : ChainIndex p) : A (m + p) :=
  includeCoefficients p (m + p) (Nat.le_add_left p m)
      (MvPolynomial.monomial t.1 (1 : ℚ)) •
    chainBasis (m + p) (t.2.map (Fin.natAddEmb m))

theorem passiveMonomial_cycle (N m p : ℕ) (hN : 0 < N) (t : ChainIndex p) :
    CoefficientComplex.d N (m + p) (N * (m + p) - m) (passiveMonomial m p t) = 0 := by
  unfold passiveMonomial
  rw [map_smul]
  suffices he : CoefficientComplex.d N (m + p) (N * (m + p) - m)
      (chainBasis (m + p) (t.2.map (Fin.natAddEmb m))) = 0 by
    rw [he, smul_zero]
  rw [chainBasis_eq_sort_prod]
  have hl : ∀ x ∈ ((t.2.map (Fin.natAddEmb m)).sort.map (xi (m + p))),
      CoefficientComplex.d N (m + p) (N * (m + p) - m) x = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' : i ∈ t.2.map (Fin.natAddEmb m) := by simpa using hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi'
    exact passive_d_xi N m (m + p) hN (Nat.le_add_right m p) _ (by simp)
  generalize he : ((t.2.map (Fin.natAddEmb m)).sort.map (xi (m + p))) = l at hl ⊢
  clear he
  induction l with
  | nil => exact (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).d_one
  | cons x xs ih =>
    simp only [List.prod_cons]
    exact (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).d_mul_eq_zero
      (hl x (by simp)) (ih (by intro y hy; exact hl y (by simp [hy])))

theorem blockCoefficients_eq_rename (m p : ℕ) (c : R m) :
    activeCoefficients m (m + p) (Nat.le_add_right m p)
      (TorusLinkHomology.Reversal.reverseCoefficients m c) =
      MvPolynomial.rename (highPolynomialIndex m p) c := by
  induction c using MvPolynomial.induction_on with
  | C q =>
    simp [activeCoefficients, includeCoefficients, TorusLinkHomology.Reversal.reverseCoefficients,
      MvPolynomial.renameEquiv]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X c i ih =>
    change activeCoefficients m (m + p) _
      (TorusLinkHomology.Reversal.reverseCoefficients m (c * u m i)) = _
    rw [map_mul, map_mul, ih, blockCoefficients_u, map_mul]
    congr 1
    simp [u]

theorem blockChains_smul (m p : ℕ) (c : R m) (x : A m) :
    blockChains m p (c • x) = MvPolynomial.rename (highPolynomialIndex m p) c •
      blockChains m p x := by
  simp only [blockChains, RingHom.comp_apply, TorusLinkHomology.Reversal.reverseChains_smul,
    activeChains_smul, blockCoefficients_eq_rename]

@[simp] theorem blockChains_chainBasis (m p : ℕ) (s : Finset (Fin m)) :
    blockChains m p (chainBasis m s) =
      chainBasis (m + p) (s.map (Fin.castAddEmb p)) := by
  classical
  rw [chainBasis_eq_sort_prod, chainBasis_eq_sort_prod, map_list_prod, List.map_map]
  have hs : s.sort.map (Fin.castAddEmb p) = (s.map (Fin.castAddEmb p)).sort :=
    Finset.map_sort _ _ _ _ (by intro a ha b hb; exact Iff.rfl)
  rw [← hs, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact blockChains_xi m p i

/-- Exterior monomials multiply without a sign when their blocks are ordered. -/
theorem chainBasis_mul_of_separated (r : ℕ) (s t : Finset (Fin r))
    (hst : ∀ i ∈ s, ∀ j ∈ t, i < j) :
    chainBasis r s * chainBasis r t = chainBasis r (s ∪ t) := by
  classical
  have hs : (s ∪ t).sort = s.sort ++ t.sort := by
    apply (Finset.sortedLT_sort _).eq_of_mem_iff
    · apply List.Pairwise.sortedLT
      apply List.pairwise_append.mpr
      refine ⟨(Finset.sortedLT_sort _).pairwise, (Finset.sortedLT_sort _).pairwise, ?_⟩
      intro i hi j hj
      exact hst i (by simpa using hi) j (by simpa using hj)
    · intro i
      simp
  simp only [chainBasis_eq_sort_prod, hs, List.map_append, List.prod_append]

@[simp] theorem splitPolynomialIndex_active (m p : ℕ) (q : Fin (m + p) →₀ ℕ) (i : Fin m) :
    (splitPolynomialIndex m p q).1 i = q (highPolynomialIndex m p i) := by
  simp [splitPolynomialIndex, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply,
    highPolynomialIndex]
  congr 1
  apply Fin.ext
  change i.val + p = p + i.val
  omega

@[simp] theorem splitPolynomialIndex_passive (m p : ℕ) (q : Fin (m + p) →₀ ℕ) (i : Fin p) :
    (splitPolynomialIndex m p q).2 i = q (lowPolynomialIndex m p i) := by
  simp [splitPolynomialIndex, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply,
    lowPolynomialIndex]
  congr 1

@[simp] theorem mem_splitExteriorIndex_active (m p : ℕ) (s : Finset (Fin (m + p))) (i : Fin m) :
    i ∈ (splitExteriorIndex m p s).1 ↔ Fin.castAdd p i ∈ s := by
  simp [splitExteriorIndex, Equiv.finsetCongr_apply]

@[simp] theorem mem_splitExteriorIndex_passive (m p : ℕ) (s : Finset (Fin (m + p))) (i : Fin p) :
    i ∈ (splitExteriorIndex m p s).2 ↔ Fin.natAdd m i ∈ s := by
  simp [splitExteriorIndex, Equiv.finsetCongr_apply]

/-- Reassemble polynomial/exterior indices in their respective block orders. -/
def combineChainIndex (m p : ℕ) (t : ChainIndex p) (q : ChainIndex m) : ChainIndex (m + p) :=
  (q.1.mapDomain (highPolynomialIndex m p) + t.1.mapDomain (lowPolynomialIndex m p),
    q.2.map (Fin.castAddEmb p) ∪ t.2.map (Fin.natAddEmb m))

private theorem mapDomain_high_at_low (m p : ℕ) (q : Fin m →₀ ℕ) (j : Fin p) :
    q.mapDomain (highPolynomialIndex m p) (lowPolynomialIndex m p j) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i, hi⟩
  have he := congrArg Fin.val hi
  change p + i.val = j.val at he
  have := j.isLt
  omega

private theorem mapDomain_low_at_high (m p : ℕ) (t : Fin p →₀ ℕ) (i : Fin m) :
    t.mapDomain (lowPolynomialIndex m p) (highPolynomialIndex m p i) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, hj⟩
  have he := congrArg Fin.val hj
  change j.val = p + i.val at he
  have := j.isLt
  omega

@[simp] theorem split_combineChainIndex (m p : ℕ) (t : ChainIndex p) (q : ChainIndex m) :
    splitChainIndex m p (combineChainIndex m p t q) = (t, q) := by
  apply Prod.ext
  · apply Prod.ext
    · ext i
      change (splitPolynomialIndex m p (combineChainIndex m p t q).1).2 i = t.1 i
      rw [splitPolynomialIndex_passive]
      simp only [combineChainIndex, Finsupp.add_apply, mapDomain_high_at_low,
        Finsupp.mapDomain_apply (lowPolynomialIndex m p).injective, zero_add]
    · ext i
      change i ∈ (splitExteriorIndex m p (combineChainIndex m p t q).2).2 ↔ i ∈ t.2
      rw [mem_splitExteriorIndex_passive]
      simp only [combineChainIndex, Finset.mem_union, Finset.mem_map]
      constructor
      · rintro (⟨j, hj, he⟩ | ⟨j, hj, he⟩)
        · have hv := congrArg Fin.val he
          change j.val = m + i.val at hv
          have := j.isLt
          omega
        · have hji : j = i := (Fin.natAddEmb m).injective he
          simpa only [hji] using hj
      · intro hi
        exact Or.inr ⟨i, hi, rfl⟩
  · apply Prod.ext
    · ext i
      change (splitPolynomialIndex m p (combineChainIndex m p t q).1).1 i = q.1 i
      rw [splitPolynomialIndex_active]
      simp only [combineChainIndex, Finsupp.add_apply, mapDomain_low_at_high,
        Finsupp.mapDomain_apply (highPolynomialIndex m p).injective, add_zero]
    · ext i
      change i ∈ (splitExteriorIndex m p (combineChainIndex m p t q).2).1 ↔ i ∈ q.2
      rw [mem_splitExteriorIndex_active]
      simp only [combineChainIndex, Finset.mem_union, Finset.mem_map]
      constructor
      · rintro (⟨j, hj, he⟩ | ⟨j, hj, he⟩)
        · have hji : j = i := (Fin.castAddEmb p).injective he
          simpa only [hji] using hj
        · have hv := congrArg Fin.val he
          change m + j.val = i.val at hv
          have := i.isLt
          omega
      · intro hi
        exact Or.inl ⟨i, hi, rfl⟩

@[simp] theorem decomposeChains_symm_single_basis (m p : ℕ) (t : ChainIndex p) (q : ChainIndex m) :
    (decomposeChains m p).symm (Finsupp.single t (activeBasis m q)) =
      rationalChainBasis (m + p) (combineChainIndex m p t q) := by
  apply (decomposeChains m p).injective
  rw [LinearEquiv.apply_symm_apply, decomposeChains_basis, split_combineChainIndex]

/-- On the monomial basis, the decomposition is multiplication by the passive factor. -/
theorem basis_combine_eq_mul (m p : ℕ) (t : ChainIndex p) (q : ChainIndex m) :
    rationalChainBasis (m + p) (combineChainIndex m p t q) =
      activeChains m (m + p) (Nat.le_add_right m p) (activeBasis m q) *
        passiveMonomial m p t := by
  change rationalChainBasis (m + p) (combineChainIndex m p t q) =
    blockChains m p (rationalChainBasis m q) * passiveMonomial m p t
  rw [rationalChainBasis_apply m, blockChains_smul, blockChains_chainBasis]
  have hs : chainBasis (m + p) (q.2.map (Fin.castAddEmb p)) *
      chainBasis (m + p) (t.2.map (Fin.natAddEmb m)) =
      chainBasis (m + p) (q.2.map (Fin.castAddEmb p) ∪ t.2.map (Fin.natAddEmb m)) := by
    apply chainBasis_mul_of_separated
    intro i hi j hj
    obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
    change i'.val < m + j'.val
    have := i'.isLt
    omega
  change rationalChainBasis (m + p) (combineChainIndex m p t q) =
    (MvPolynomial.rename (highPolynomialIndex m p) (MvPolynomial.monomial q.1 1) •
      chainBasis (m + p) (q.2.map (Fin.castAddEmb p))) *
    (MvPolynomial.rename (lowPolynomialIndex m p) (MvPolynomial.monomial t.1 1) •
      chainBasis (m + p) (t.2.map (Fin.natAddEmb m)))
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hs,
    MvPolynomial.rename_monomial, MvPolynomial.rename_monomial,
    MvPolynomial.monomial_mul, one_mul]
  exact rationalChainBasis_apply _ _

/-- Explicit inverse of the decomposition on each passive summand. -/
theorem decomposeChains_symm_single (m p : ℕ) (t : ChainIndex p) (x : A m) :
    (decomposeChains m p).symm (Finsupp.single t x) =
      activeChains m (m + p) (Nat.le_add_right m p) x * passiveMonomial m p t := by
  let left : A m →ₗ[ℚ] A (m + p) :=
    (decomposeChains m p).symm.toLinearMap.comp (Finsupp.lsingle t)
  let right : A m →ₗ[ℚ] A (m + p) :=
    (LinearMap.mulRight ℚ (passiveMonomial m p t)).comp
      (activeChains m (m + p) (Nat.le_add_right m p)).toAddMonoidHom.toRatLinearMap
  have he : left = right := by
    apply (activeBasis m).ext
    intro q
    exact (decomposeChains_symm_single_basis m p t q).trans (basis_combine_eq_mul m p t q)
  exact LinearMap.congr_fun he x

/-- Passive monomials have zero differential, so each summand carries exactly
one copy of the original differential, with no sign shift. -/
theorem d_decomposeChains_symm_single (N m p : ℕ) (hN : 0 < N)
    (t : ChainIndex p) (x : A m) :
    CoefficientComplex.d N (m + p) (N * (m + p) - m)
      ((decomposeChains m p).symm (Finsupp.single t x)) =
      (decomposeChains m p).symm (Finsupp.single t (d N m x)) := by
  rw [decomposeChains_symm_single,
    (CoefficientComplex.dga N (m + p) (N * (m + p) - m)).d_mul_of_cycle
      (passiveMonomial_cycle N m p hN t), activeChains_d N m (m + p) hN,
    decomposeChains_symm_single]

/-- The full inverse decomposition intertwines the differential componentwise. -/
theorem d_decomposeChains_symm (N m p : ℕ) (hN : 0 < N)
    (f : ChainIndex p →₀ A m) :
    CoefficientComplex.d N (m + p) (N * (m + p) - m)
      ((decomposeChains m p).symm f) =
      (decomposeChains m p).symm (Finsupp.mapRange (d N m) (map_zero _) f) := by
  induction f using Finsupp.induction with
  | zero => simp
  | single_add t x f ht hx ih =>
    simp only [map_add, Finsupp.mapRange_add' , Finsupp.mapRange_single,
      d_decomposeChains_symm_single N m p hN, ih]

/-- In these coordinates the auxiliary differential acts separately on every
active copy of K_m. -/
theorem decomposeChains_d (N m p : ℕ) (hN : 0 < N) (x : A (m + p)) :
    decomposeChains m p (CoefficientComplex.d N (m + p) (N * (m + p) - m) x) =
      Finsupp.mapRange (d N m) (map_zero _) (decomposeChains m p x) := by
  apply (decomposeChains m p).symm.injective
  rw [LinearEquiv.symm_apply_apply, ← d_decomposeChains_symm N m p hN,
    LinearEquiv.symm_apply_apply]

/-- Cycle detection is componentwise in the passive-monomial decomposition. -/
theorem auxiliary_cycle_iff_components (N m p : ℕ) (hN : 0 < N) (x : A (m + p)) :
    CoefficientComplex.d N (m + p) (N * (m + p) - m) x = 0 ↔
      ∀ t, d N m (decomposeChains m p x t) = 0 := by
  rw [← (decomposeChains m p).map_eq_zero_iff, decomposeChains_d N m p hN]
  constructor
  · intro he t
    exact DFunLike.congr_fun he t
  · intro he
    ext t
    exact he t

end TorusLinkHomology.HilbertSeries.GeneralReversal
