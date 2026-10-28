import TorusLinkHomology.Generation.ShortRangeCycles
import DGA.ExteriorProducts
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Finite universal jet expressions

We use divided coordinates: `U_j = j! u_j` and `Y_j = j! ξ_j`.
The expression `D^i p(D)Y` is defined by its finite coefficient formula;
no derivation on a truncated jet algebra is assumed. The degree bound on
`p` ensures that none of the required jets is discarded.
-/

noncomputable section

namespace TorusLinkHomology.UniversalJets

open scoped BigOperators

/-- All coefficients of the N-th power have polynomial degree N,
independently of their coefficient-variable index. -/
theorem uPolynomial_pow_coeff_isHomogeneous (N n j : ℕ) :
    ((uPolynomial n ^ N).coeff j).IsHomogeneous N := by
  have hu (j : ℕ) : ((uPolynomial n).coeff j).IsHomogeneous 1 := by
    rw [uPolynomial, Polynomial.finsetSum_coeff]
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    rw [Polynomial.coeff_monomial]
    split_ifs
    · exact MvPolynomial.isHomogeneous_X ℚ i
    · exact MvPolynomial.isHomogeneous_zero (Fin n) ℚ 1
  induction N generalizing j with
  | zero =>
    simp only [pow_zero, Polynomial.coeff_one]
    split_ifs
    · exact MvPolynomial.isHomogeneous_one (Fin n) ℚ
    · exact MvPolynomial.isHomogeneous_zero (Fin n) ℚ 0
  | succ N ih =>
    rw [pow_succ, Polynomial.coeff_mul]
    apply MvPolynomial.IsHomogeneous.sum
    intro ij _
    exact (ih ij.1).mul (hu ij.2)

theorem differentialCoefficient_isHomogeneous (N n : ℕ) (j : Fin n) :
    (differentialCoefficient N n j).IsHomogeneous N :=
  uPolynomial_pow_coeff_isHomogeneous N n j.val

/-- Coefficient of `Y_j` in the formal expression `D^i p(D)Y`. -/
def jetCoefficient (p : Polynomial ℚ) (i j : ℕ) : ℚ :=
  if i ≤ j then p.coeff (j - i) * (j.factorial : ℚ) else 0

/-- The finite vector representing `D^i p(D)Y`, in divided coordinates. -/
def jetVector (N : ℕ) (p : Polynomial ℚ) (i : ℕ) : V (N + 1) :=
  ∑ j : Fin (N + 1),
    algebraMap ℚ (R (N + 1)) (jetCoefficient p i j.val) • Finsupp.single j 1

/-- The matching expression `D^i p(D)(U^N)`. -/
def jetDifferential (N : ℕ) (p : Polynomial ℚ) (i : ℕ) : R (N + 1) :=
  ∑ j : Fin (N + 1),
    algebraMap ℚ (R (N + 1)) (jetCoefficient p i j.val) *
      differentialCoefficient N (N + 1) j

theorem jetDifferential_isHomogeneous (N : ℕ) (p : Polynomial ℚ) (i : ℕ) :
    (jetDifferential N p i).IsHomogeneous N := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (differentialCoefficient_isHomogeneous N (N + 1) j).C_mul _

theorem jetCoefficient_eq_zero_of_large_index (N q : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree + q ≤ N) {i j : ℕ} (hi : i ≤ q) (hj : N < j) :
    jetCoefficient p i j = 0 := by
  have hdegree : p.natDegree < j - i := by omega
  simp [jetCoefficient, Polynomial.coeff_eq_zero_of_natDegree_lt hdegree]

@[simp] theorem differentialFunctional_jetVector (N : ℕ) (p : Polynomial ℚ) (i : ℕ) :
    differentialFunctional N (N + 1) (jetVector N p i) = jetDifferential N p i := by
  simp [jetVector, jetDifferential, differentialFunctional, Finsupp.linearCombination_single]

/-- The ordered product of the `q+1` odd selector expressions. -/
def selectorProduct (N q : ℕ) (p : Polynomial ℚ) : A (N + 1) :=
  ExteriorAlgebra.ιMulti (R (N + 1)) (q + 1) (fun i => jetVector N p i.val)

/-- The alternating deletion expression `T_p(U^N;Y)`. -/
def selectorCycle (N q : ℕ) (p : Polynomial ℚ) : A (N + 1) :=
  ∑ i : Fin (q + 1),
    ((-1 : R (N + 1)) ^ i.val * jetDifferential N p i.val) •
      ExteriorAlgebra.ιMulti (R (N + 1)) q
        ((fun j : Fin (q + 1) => jetVector N p j.val) ∘ i.succAbove)

/-- The order and signs in the universal expression are the Koszul signs. -/
theorem d_selectorProduct (N q : ℕ) (p : Polynomial ℚ) :
    d N (N + 1) (selectorProduct N q p) = selectorCycle N q p := by
  unfold d selectorProduct selectorCycle
  rw [ExteriorAlgebra.contractLeft_ιMulti]
  simp only [differentialFunctional_jetVector]

theorem selectorCycle_is_cycle (N q : ℕ) (p : Polynomial ℚ) :
    d N (N + 1) (selectorCycle N q p) = 0 := by
  rw [← d_selectorProduct]
  exact d_squared N (N + 1) _

theorem selectorCycle_mem_degree (N q : ℕ) (p : Polynomial ℚ) :
    selectorCycle N q p ∈ koszulDegree (N + 1) q := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact ExteriorAlgebra.ιMulti_range (R (N + 1)) q ⟨_, rfl⟩

/-- Polynomial adapted coordinates of the universal selector cycle.
The projection identity removes the auxiliary coordinate, leaving only
ordered products of the named one-cycles. -/
theorem existsUnique_selector_coordinates (N q : ℕ) (p : Polynomial ℚ) :
    ∃! w : PiCoordinates.PiA (N + 1),
      ExteriorAlgebra.map (Generation.muAdjoinedMatrix N N 0).toLin' w =
        PiCoordinates.toPi (N + 1) (selectorCycle N q p) ∧
      ExteriorAlgebra.map (Generation.eraseCoordinate 0) w = w := by
  exact Generation.existsUnique_mu_cycle_coordinates N N le_rfl _
    (selectorCycle_is_cycle N q p)

end TorusLinkHomology.UniversalJets
