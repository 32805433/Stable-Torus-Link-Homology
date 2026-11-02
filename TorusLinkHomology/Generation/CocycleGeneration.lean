import TorusLinkHomology.Generation.AuxiliaryInduction
import TorusLinkHomology.Generation.ReversedGenerators
import TorusLinkHomology.Generation.ChainIdentity

/-!
# Generation of coefficient Koszul homology

This supporting cocycle theorem supplies representatives for the public
DGA homology-generation theorem. The proof uses coefficient reversal, auxiliary induction,
and the chain identity for exceptional products.
-/

namespace TorusLinkHomology

/-- The named one-cycles generate every cycle modulo boundaries. -/
theorem cycles_generated_by_mu_mod_boundaries (n N : ℕ) (hN : 0 < N) :
  (∀ k : ℕ, 1 ≤ k → k < n → d N n (mu N n k) = 0) ∧
  (∀ a : A n, d N n a = 0 →
    ∃ p : A n, p ∈ muSubalgebra N n ∧ ∃ b : A n, a = p + d N n b) := by
  by_cases hn0 : n = 0
  · subst n
    exact Generation.zero_variables N
  -- Positive lengths use the auxiliary-complex argument uniformly.
  -- Exponent one reaches its offset-zero induction base under reversal.
  apply Reversal.cycleGeneration_of_tailGeneration N n hN (Nat.pos_of_ne_zero hn0)
  apply CoefficientComplex.tailGeneration_of_all_exceptionalTransfers N hN
  intro r ell hm
  exact CoefficientComplex.exceptionalTransfers_of_continuation N r ell hN hm

end TorusLinkHomology
