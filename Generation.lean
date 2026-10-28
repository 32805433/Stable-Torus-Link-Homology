import TorusLinkHomology.Generation.CocycleGeneration
import TorusLinkHomology.Generation.Equivalence

/-! Public DGA homology-generation theorem, with the exact Challenge statement. -/

namespace TorusLinkHomology

/-- The named elements μ₁,…,μₙ₋₁ are cycles whose classes generate the
DGA homology as an algebra over R n. The cycle representatives are bundled
with generation so that no separate admitted cycle lemma is needed. -/
theorem homology_generated_by_mu (n N : ℕ) (hN : 0 < N) :
    ∃ c : {k : ℕ // 1 ≤ k ∧ k < n} → (torusLinkDGA N n).cycles,
      (∀ k, (c k : A n) = mu N n k.val) ∧
      Algebra.adjoin (R n)
        (Set.range fun k => (torusLinkDGA N n).homologyClass (c k)) = ⊤ := by
  refine ⟨muCycle N n, fun _ => rfl, ?_⟩
  exact (equivalence n N hN).mp
    (cycles_generated_by_mu_mod_boundaries n N hN)

end TorusLinkHomology
