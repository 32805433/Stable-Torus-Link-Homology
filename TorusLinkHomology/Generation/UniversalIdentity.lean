import TorusLinkHomology.Generation.UniversalJetGrading
import TorusLinkHomology.Generation.MuExpansion

/-! # The finite universal exterior identity

Ordered products of differentiated jet cycles use only nonzero rational
factorial rescalings of the named cycle basis.
-/

noncomputable section

namespace TorusLinkHomology.UniversalJets

open scoped BigOperators
open Generation

/-- The ordinary differentiated jet cycles in increasing positive-index order.
An index j denotes the derivative of order j−1. -/
def orderedJetProduct (N n : ℕ) (s : Finset (Fin n)) : A n :=
  (s.sort.map (fun j => bDerivative N n (j.val - 1))).prod

/-- The rational rescaling from the differentiated jets to the named cycles. -/
def inverseFactorialProduct (n : ℕ) (s : Finset (Fin n)) : ℚ :=
  (s.sort.map (fun j => -(((j.val - 1).factorial : ℚ)⁻¹))).prod

theorem inverseFactorialProduct_ne_zero (n : ℕ) (s : Finset (Fin n)) :
    inverseFactorialProduct n s ≠ 0 := by
  apply List.prod_ne_zero
  intro hc
  obtain ⟨j, _, hj⟩ := List.mem_map.mp hc
  exact (neg_ne_zero.mpr (inv_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j.val - 1))))) hj

private theorem mu_listProduct_eq (N n : ℕ) (l : List (Fin n))
    (hl : ∀ j ∈ l, 0 < j.val) :
    (l.map (fun j => mu N n j.val)).prod =
      algebraMap ℚ (R n) (l.map (fun j => -(((j.val - 1).factorial : ℚ)⁻¹))).prod •
        (l.map (fun j => bDerivative N n (j.val - 1))).prod := by
  induction l with
  | nil => simp
  | cons j l ih =>
    have hj : 1 ≤ j.val := hl j (by simp)
    have hmu : mu N n j.val =
        algebraMap ℚ (R n) (-(((j.val - 1).factorial : ℚ)⁻¹)) •
          bDerivative N n (j.val - 1) := by
      simpa only [Nat.sub_add_cancel hj] using
        mu_eq_invFactorial_smul_bDerivative N n (j.val - 1)
    simp only [List.map_cons, List.prod_cons, hmu,
      ih (fun i hi => hl i (by simp [hi])), map_mul]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/-- The positive-index μ product is a rational multiple of the ordinary jet
product, with both products in precisely the same order. -/
theorem mu_sortedProduct_eq (N a : ℕ) (s : Finset (Fin (a + 1))) (hzero : 0 ∉ s) :
    (s.sort.map (fun j => mu N (a + 1) j.val)).prod =
      algebraMap ℚ (R (a + 1)) (inverseFactorialProduct (a + 1) s) •
        orderedJetProduct N (a + 1) s := by
  apply mu_listProduct_eq
  intro j hj
  have hmem : j ∈ s := by simpa using hj
  have hj0 : j ≠ 0 := fun h => hzero (h ▸ hmem)
  have : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
  omega

/-- The inverse change of ordered basis uses rational scalars only. -/
theorem orderedJetProduct_eq (N a : ℕ) (s : Finset (Fin (a + 1))) (hzero : 0 ∉ s) :
    orderedJetProduct N (a + 1) s =
      algebraMap ℚ (R (a + 1)) (inverseFactorialProduct (a + 1) s)⁻¹ •
        orderedMuProduct N a s := by
  have h := mu_sortedProduct_eq N a s hzero
  change orderedMuProduct N a s = _ at h
  rw [h, smul_smul, ← map_mul,
    inv_mul_cancel₀ (inverseFactorialProduct_ne_zero (a + 1) s), map_one, one_smul]

/-- The literal finite polynomial identity in the named cycle basis,
including uniqueness, polynomial degree, and the exact exterior support. -/
theorem selector_mu_identity (N q : ℕ) (p : Polynomial ℚ) (hq : q ≤ N) :
    ∃! c : Finset (Fin (N + 1)) → R (N + 1),
      (∀ s, (c s).IsHomogeneous (N - q)) ∧
      (∀ s, (0 : Fin (N + 1)) ∈ s ∨ s.card ≠ q → c s = 0) ∧
      selectorCycle N q p = ∑ s : Finset (Fin (N + 1)), c s • orderedMuProduct N N s := by
  obtain ⟨w, hw, hp, hdegree, hcard⟩ := exists_homogeneous_selector_coordinates N q p hq
  let c : Finset (Fin (N + 1)) → R (N + 1) :=
    fun s => (Pi.basisFun (R (N + 1)) (Fin (N + 1))).ExteriorAlgebra.repr w s
  have hzero : ∀ s, (0 : Fin (N + 1)) ∈ s → c s = 0 :=
    repr_eq_zero_of_eraseCoordinate_fixed 0 w hp
  have hexp : selectorCycle N q p = ∑ s : Finset (Fin (N + 1)), c s • orderedMuProduct N N s := by
    rw [← piMuMap_eq_of_coordinates N N hw hp, piMuMap_eq_sum_orderedMuProduct]
  refine ⟨c, ⟨hdegree, ?_, hexp⟩, ?_⟩
  · intro s hs
    rcases hs with hs | hs
    · exact hzero s hs
    · exact hcard s hs
  · intro c' hc'
    exact orderedMuProduct_coefficients_unique N N c' c
      (fun s hs => hc'.2.1 s (Or.inl hs)) hzero (hc'.2.2.symm.trans hexp)

private theorem jet_sum_eq_mu_sum (N a : ℕ) (c : Finset (Fin (a + 1)) → R (a + 1))
    (hc : ∀ s, (0 : Fin (a + 1)) ∈ s → c s = 0) :
    (∑ s : Finset (Fin (a + 1)), c s • orderedJetProduct N (a + 1) s) =
      ∑ s : Finset (Fin (a + 1)),
        (algebraMap ℚ (R (a + 1)) (inverseFactorialProduct (a + 1) s)⁻¹ * c s) •
          orderedMuProduct N a s := by
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : (0 : Fin (a + 1)) ∈ s
  · rw [hc s hs, zero_smul, mul_zero, zero_smul]
  · rw [orderedJetProduct_eq N a s hs, smul_smul, mul_comm]

/-- Independence of the differentiated jet products over the polynomial ring. -/
theorem orderedJetProduct_coefficients_unique (N a : ℕ)
    (c d : Finset (Fin (a + 1)) → R (a + 1))
    (hc : ∀ s, (0 : Fin (a + 1)) ∈ s → c s = 0)
    (hd : ∀ s, (0 : Fin (a + 1)) ∈ s → d s = 0)
    (h : (∑ s : Finset (Fin (a + 1)), c s • orderedJetProduct N (a + 1) s) =
      ∑ s : Finset (Fin (a + 1)), d s • orderedJetProduct N (a + 1) s) : c = d := by
  rw [jet_sum_eq_mu_sum N a c hc, jet_sum_eq_mu_sum N a d hd] at h
  have heq := orderedMuProduct_coefficients_unique N a _ _
    (fun s hs => by rw [hc s hs, mul_zero]) (fun s hs => by rw [hd s hs, mul_zero]) h
  funext s
  have hs := congrFun heq s
  have hnonzero : algebraMap ℚ (R (a + 1)) (inverseFactorialProduct (a + 1) s)⁻¹ ≠ 0 :=
    (map_ne_zero (algebraMap ℚ (R (a + 1)))).mpr
      (inv_ne_zero (inverseFactorialProduct_ne_zero (a + 1) s))
  exact mul_left_cancel₀ hnonzero hs

/-- The finite universal exterior identity in ordinary differentiated jets.
All coefficients are polynomials, homogeneous of degree N−q, and are unique
in the ordered q-fold jet basis. No polynomial variable is inverted. -/
theorem universal_exterior_identity (N q : ℕ) (p : Polynomial ℚ) (hq : q ≤ N) :
    ∃! c : Finset (Fin (N + 1)) → R (N + 1),
      (∀ s, (c s).IsHomogeneous (N - q)) ∧
      (∀ s, (0 : Fin (N + 1)) ∈ s ∨ s.card ≠ q → c s = 0) ∧
      selectorCycle N q p =
        ∑ s : Finset (Fin (N + 1)), c s • orderedJetProduct N (N + 1) s := by
  obtain ⟨c, hc, _⟩ := selector_mu_identity N q p hq
  let b : Finset (Fin (N + 1)) → R (N + 1) := fun s =>
    algebraMap ℚ (R (N + 1)) (inverseFactorialProduct (N + 1) s) * c s
  have hbzero : ∀ s, (0 : Fin (N + 1)) ∈ s ∨ s.card ≠ q → b s = 0 := by
    intro s hs
    simp only [b, hc.2.1 s hs, mul_zero]
  have hexp : selectorCycle N q p =
      ∑ s : Finset (Fin (N + 1)), b s • orderedJetProduct N (N + 1) s := by
    rw [hc.2.2]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : (0 : Fin (N + 1)) ∈ s
    · rw [hc.2.1 s (Or.inl hs), hbzero s (Or.inl hs), zero_smul, zero_smul]
    · rw [orderedMuProduct, mu_sortedProduct_eq N N s hs, smul_smul, mul_comm]
  refine ⟨b, ⟨?_, hbzero, hexp⟩, ?_⟩
  · intro s
    exact (hc.1 s).C_mul _
  · intro b' hb'
    exact orderedJetProduct_coefficients_unique N N b' b
      (fun s hs => hb'.2.1 s (Or.inl hs)) (fun s hs => hbzero s (Or.inl hs))
      (hb'.2.2.symm.trans hexp)

end TorusLinkHomology.UniversalJets
