import TorusLinkHomology.Generation.CoefficientComplex
import TorusLinkHomology.Generation.PiCoordinates
import DGA.ExteriorPiBaseChange

/-!
# The coefficient complex over a field of fractions

The continuation of the tail recurrence divides by the last coefficient, so it
lives after extending scalars to a field containing `R r`. For a fraction field
this extension is injective on chains, and an identity found there descends.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientComplex

variable (r : ℕ) (F : Type*) [Field F] [Algebra (R r) F]

/-- Degree-one chains over the larger coefficient field, in standard coordinates. -/
abbrev VF := Fin r → F

/-- Chains over the larger coefficient field. -/
abbrev AF := ExteriorAlgebra F (VF r F)

/-- Extension of scalars on degree-one chains. -/
def vecF : V r →ₛₗ[algebraMap (R r) F] VF r F :=
  (ExteriorAlgebra.piScalarMap (algebraMap (R r) F)).comp
    (PiCoordinates.vectorEquiv r).toLinearMap

/-- Extension of scalars on all chains. -/
def toF : A r →+* AF r F :=
  ExteriorAlgebra.mapOfSemilinear (algebraMap (R r) F) (vecF r F)

variable {r F}

@[simp] theorem toF_iota (v : V r) :
    toF r F (ExteriorAlgebra.ι (R r) v) = ExteriorAlgebra.ι F (vecF r F v) :=
  ExteriorAlgebra.mapOfSemilinear_iota _ _ _

@[simp] theorem toF_algebraMap (c : R r) :
    toF r F (algebraMap (R r) (A r) c) = algebraMap F (AF r F) (algebraMap (R r) F c) :=
  ExteriorAlgebra.mapOfSemilinear_algebraMap _ _ _

theorem toF_smul (c : R r) (x : A r) :
    toF r F (c • x) = algebraMap (R r) F c • toF r F x :=
  ExteriorAlgebra.mapOfSemilinear_smul _ _ _ _

/-- The extension factors through standard coordinates. -/
theorem toF_eq_piBaseChange (x : A r) :
    toF r F x = ExteriorAlgebra.piBaseChange (algebraMap (R r) F) (PiCoordinates.toPi r x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c =>
    simp only [toF_algebraMap, AlgEquiv.commutes, ExteriorAlgebra.piBaseChange,
      ExteriorAlgebra.mapOfSemilinear_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul v x hx =>
    simp only [map_mul, toF_iota, PiCoordinates.toPi_iota, ExteriorAlgebra.piBaseChange_iota, hx]
    rfl

/-- Over a fraction field, extension of scalars loses nothing. -/
theorem toF_injective [IsFractionRing (R r) F] : Function.Injective (toF r F) := by
  intro x y hxy
  rw [toF_eq_piBaseChange, toF_eq_piBaseChange] at hxy
  exact (PiCoordinates.toPi r).injective
    (ExteriorAlgebra.piBaseChange_injective _ (IsFractionRing.injective (R r) F) hxy)

variable (F) in
/-- The differential functional of the complex at offset `ell`, over `F`. -/
def functionalF (N r ell : ℕ) [Algebra (R r) F] : Module.Dual F (VF r F) :=
  ∑ i : Fin r, algebraMap (R r) F (G N r (ell + i.val + 1)) • LinearMap.proj i

theorem functionalF_vecF (N ell : ℕ) (v : V r) :
    functionalF F N r ell (vecF r F v) =
      algebraMap (R r) F (differentialFunctional N r ell v) := by
  simp only [functionalF, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    differentialFunctional, Finsupp.linearCombination_apply, smul_eq_mul]
  rw [Finsupp.sum_fintype _ _ (fun i => zero_mul _), map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, mul_comm]
  rfl

variable (F) in
/-- The differential at offset `ell`, over `F`. -/
def dF (N r ell : ℕ) [Algebra (R r) F] : AF r F →ₗ[F] AF r F :=
  CliffordAlgebra.contractLeft (Q := 0) (functionalF F N r ell)

/-- Extension of scalars commutes with the differential. -/
theorem toF_d (N ell : ℕ) (x : A r) :
    toF r F (d N r ell x) = dF F N r ell (toF r F x) :=
  (ExteriorAlgebra.contractLeft_mapOfSemilinear (algebraMap (R r) F) (vecF r F)
    (differentialFunctional N r ell) (functionalF F N r ell)
    (functionalF_vecF N ell) x).symm

end TorusLinkHomology.CoefficientComplex
