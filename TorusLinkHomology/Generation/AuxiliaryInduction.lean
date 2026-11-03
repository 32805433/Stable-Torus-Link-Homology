import TorusLinkHomology.Generation.ExceptionalGeneration
import TorusLinkHomology.Generation.AuxiliaryZeroOffset

/-!
# Auxiliary induction from finite exceptional transfers

Strong induction on rank plus offset uses the coordinate-Koszul offset-zero
calculation and the vanishing of coefficients above the polynomial degree.
The interior step uses the finite exceptional-product transfer statement,
proved independently in `ChainIdentity`.
-/

namespace TorusLinkHomology.CoefficientComplex

/-- Finite exceptional-product transfers imply tail generation at every
rank and offset. -/
theorem tailGeneration_of_all_exceptionalTransfers (N : ℕ) (hN : 0 < N)
    (htransfers : ∀ r ell : ℕ, ell + 1 < N * (r + 1) → ExceptionalTransfers N r ell)
    (r ell : ℕ) : TailGeneration N r ell := by
  generalize hk : r + ell = k
  induction k using Nat.strong_induction_on generalizing r ell with
  | h k ih =>
    cases ell with
    | zero => exact tailGeneration_zero_offset N r hN
    | succ ell =>
      by_cases hhigh : N * r ≤ ell + 1
      · exact tailGeneration_of_le N r (ell + 1) hhigh
      · cases r with
        | zero => exact (hhigh (by simp)).elim
        | succ r =>
          have hm : ell + 1 < N * (r + 1) := Nat.lt_of_not_ge hhigh
          apply tailGeneration_of_exceptionalTransfers N r ell hm
          · exact ih ((r + 1) + ell) (by omega) (r + 1) ell rfl
          · exact ih (r + (ell + 1)) (by omega) r (ell + 1) rfl
          · exact htransfers r ell hm

end TorusLinkHomology.CoefficientComplex
