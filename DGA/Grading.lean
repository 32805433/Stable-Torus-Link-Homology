import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous components of cycles

An integer-graded linear map of degree `-1` commutes with the homogeneous
projections after shifting their indices. In particular, every homogeneous
component of an element in its kernel also lies in its kernel.
-/

namespace DGA.Grading

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (grade : ℤ → Submodule R A) [GradedAlgebra grade]
variable (d : A →ₗ[R] A)
variable (d_mem : ∀ (p : ℤ) ⦃x : A⦄, x ∈ grade p → d x ∈ grade (p - 1))

include d_mem

/-- A differential of degree `-1` sends the degree `p` component to the
degree `p - 1` component of its value. -/
theorem differential_proj (p : ℤ) (x : A) :
    d (GradedAlgebra.proj grade p x) = GradedAlgebra.proj grade (p - 1) (d x) := by
  have h : d ∘ₗ GradedAlgebra.proj grade p =
      GradedAlgebra.proj grade (p - 1) ∘ₗ d := by
    apply DirectSum.decompose_lhom_ext grade
    intro q
    ext x
    change d (GradedAlgebra.proj grade p (x : A)) =
      GradedAlgebra.proj grade (p - 1) (d (x : A))
    by_cases hqp : q = p
    · subst q
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same grade x.property,
        GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same grade (d_mem p x.property)]
    · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne grade x.property hqp,
        map_zero, GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_ne grade (d_mem q x.property) (by simpa using hqp)]
  exact DFunLike.congr_fun h x

/-- Every homogeneous component of a cycle is again a cycle. -/
theorem differential_proj_eq_zero {x : A} (hx : d x = 0) (p : ℤ) :
    d (GradedAlgebra.proj grade p x) = 0 := by
  rw [differential_proj grade d d_mem, hx, map_zero]

/-- Version of `differential_proj_eq_zero` using the decomposition API. -/
theorem differential_decompose_eq_zero {x : A} (hx : d x = 0) (p : ℤ) :
    d (DirectSum.decompose grade x p : A) = 0 :=
  differential_proj_eq_zero grade d d_mem hx p

/-- Prove an additive property of cycles by checking homogeneous cycles. -/
theorem homogeneous_cycle_induction {P : A → Prop}
    (hzero : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hhom : ∀ (p : ℤ) (x : A), x ∈ grade p → d x = 0 → P x)
    {x : A} (hx : d x = 0) : P x := by
  classical
  rw [← DirectSum.sum_support_decompose grade x]
  apply Finset.sum_induction _ _ hadd hzero
  intro p _
  exact hhom p _ (DirectSum.decompose grade x p).property
    (differential_decompose_eq_zero grade d d_mem hx p)

end DGA.Grading
