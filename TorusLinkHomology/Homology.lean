import DGA.Exterior
import TorusLinkHomology.MuCycles

/-!
# The coefficient Koszul DGA and its homology classes

This module defines the actual homology algebra and named classes without
assuming or importing either homology-generation theorem.
-/

noncomputable section

namespace TorusLinkHomology

/-- The torus-link Koszul DGA over its polynomial coefficient ring. -/
def torusLinkDGA (N n : ℕ) : DGA (R n) (A n) :=
  ExteriorAlgebra.koszulDGA (R n) (V n) (differentialFunctional N n)

/-- This packages exactly the differential in the original formulation. -/
@[simp] theorem torusLinkDGA_d (N n : ℕ) : (torusLinkDGA N n).d = d N n := rfl

/-- Its total homology, with the algebra structure supplied by `DGA.Homology`. -/
abbrev Homology (N n : ℕ) := (torusLinkDGA N n).Homology

/-- Exactly the indices 1, ..., n-1. -/
abbrev MuIndex (n : ℕ) := {k : ℕ // 1 ≤ k ∧ k < n}

/-- The explicit element μₖ regarded as a cycle, using the proved coefficient identity. -/
def muCycle (N n : ℕ) (k : MuIndex n) : (torusLinkDGA N n).cycles :=
  ⟨mu N n k.val, mu_is_cycle N n k.val k.property.2⟩

@[simp] theorem coe_muCycle (N n : ℕ) (k : MuIndex n) :
    (muCycle N n k : A n) = mu N n k.val := rfl

/-- The representatives of the conjectured generators have Koszul degree one. -/
theorem muCycle_degree_one (N n : ℕ) (k : MuIndex n) :
    (muCycle N n k : A n) ∈ (torusLinkDGA N n).grading 1 := by
  change mu N n k.val ∈ ExteriorAlgebra.intGrading (R n) (V n) (1 : ℤ)
  exact mu_mem_degree_one N n k.val

/-- The actual homology class [μₖ]. -/
def muClass (N n : ℕ) (k : MuIndex n) : Homology N n :=
  (torusLinkDGA N n).homologyClass (muCycle N n k)

end TorusLinkHomology
