import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Finite homogeneous decompositions and their dimension sums. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

variable {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℚ V]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)]

/-- A finite family of mutually orthogonal inclusions and projections gives
an actual linear equivalence with the product of the component spaces. -/
def finiteDecompositionEquiv (inc : ∀ i, M i →ₗ[ℚ] V) (proj : ∀ i, V →ₗ[ℚ] M i)
    (hdiag : ∀ i x, proj i (inc i x) = x)
    (hoff : ∀ i j, i ≠ j → ∀ x, proj i (inc j x) = 0)
    (hsum : ∀ x, ∑ i, inc i (proj i x) = x) : V ≃ₗ[ℚ] (∀ i, M i) where
  toFun x i := proj i x
  invFun x := ∑ i, inc i (x i)
  left_inv := hsum
  right_inv x := by
    classical
    funext i
    change proj i (∑ j, inc j (x j)) = x i
    rw [map_sum, Finset.sum_eq_single i]
    · exact hdiag i (x i)
    · intro j hj hji
      exact hoff i j (Ne.symm hji) (x j)
    · simp
  map_add' x y := by funext i; exact map_add _ _ _
  map_smul' q x := by funext i; exact map_smul _ _ _

theorem finrank_of_finiteDecomposition [∀ i, Module.Finite ℚ (M i)]
    (inc : ∀ i, M i →ₗ[ℚ] V) (proj : ∀ i, V →ₗ[ℚ] M i)
    (hdiag : ∀ i x, proj i (inc i x) = x)
    (hoff : ∀ i j, i ≠ j → ∀ x, proj i (inc j x) = 0)
    (hsum : ∀ x, ∑ i, inc i (proj i x) = x) :
    Module.finrank ℚ V = ∑ i, Module.finrank ℚ (M i) := by
  rw [(finiteDecompositionEquiv M inc proj hdiag hoff hsum).finrank_eq]
  exact Module.finrank_pi_fintype ℚ

end TorusLinkHomology.HilbertSeries
