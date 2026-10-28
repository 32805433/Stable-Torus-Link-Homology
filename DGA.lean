import DGA.Grading
import DGA.Quotient
import Mathlib.Algebra.Ring.NegOnePow

/-!
# Differential graded algebras and their homology algebras

`DGA R A` equips an associative unital `R`-algebra `A` with an integer grading
and an `R`-linear differential of homological degree `-1`. The differential
squares to zero and satisfies the signed Leibniz rule. No commutativity of `A`,
graded commutativity, or characteristic assumption on `R` is imposed.

For `D : DGA R A`, `D.Homology` is the total homology algebra: cycles modulo
boundaries. Its `Ring` and `Algebra R` instances are inherited from the quotient
by the two-sided ideal of boundaries in the cycle algebra. `D.homologyClass` is
the canonical algebra map from cycles, and `D.homologyModuleEquiv` identifies
its underlying module with the ordinary quotient of cycles by boundaries.

The grading is part of the DGA definition. This file constructs the algebra on
total homology; it does not package the induced grading as a `GradedAlgebra`.
-/

noncomputable section

universe u v

/-- An integer-graded differential `R`-algebra, in the homological convention.

The sign `(p.negOnePow : ℤ)` is `(-1)^p`, also for negative integer degrees.
The Leibniz identity is stated for a homogeneous first factor and an arbitrary
second factor. A nonnegative DGA is modeled by setting the negative pieces to
zero; a cohomological DGA can be reindexed by negating its degrees.
-/
structure DGA (R : Type u) (A : Type v) [CommRing R] [Ring A] [Algebra R A] where
  /-- The homogeneous components of the underlying algebra. -/
  grading : ℤ → Submodule R A
  /-- The components give an internal direct-sum decomposition compatible with multiplication. -/
  gradedAlgebra : GradedAlgebra grading
  /-- The differential. -/
  d : A →ₗ[R] A
  /-- The differential squares to zero. -/
  d_squared : ∀ x, d (d x) = 0
  /-- The differential lowers degree by one. -/
  d_mem : ∀ (p : ℤ) {x : A}, x ∈ grading p → d x ∈ grading (p - 1)
  /-- The graded Leibniz identity. -/
  leibniz : ∀ (p : ℤ) {x : A}, x ∈ grading p → ∀ y : A,
    d (x * y) = d x * y + (p.negOnePow : ℤ) • (x * d y)

attribute [instance] DGA.gradedAlgebra

namespace DGA

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]
variable (D : DGA R A)

/-- The unit is closed; this follows from Leibniz and needs no characteristic assumption. -/
@[simp] theorem d_one : D.d 1 = 0 := by
  have h := D.leibniz 0 (SetLike.one_mem_graded D.grading) 1
  have h' : D.d 1 + D.d 1 = D.d 1 + 0 := by simpa using h.symm
  exact add_left_cancel h'

/-- Every element of the coefficient ring is closed. -/
@[simp] theorem d_algebraMap (r : R) : D.d (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, D.d_one, smul_zero]

/-- The homogeneous components of a cycle are cycles. -/
theorem d_component_eq_zero {x : A} (hx : D.d x = 0) (p : ℤ) :
    D.d (GradedAlgebra.proj D.grading p x) = 0 :=
  Grading.differential_proj_eq_zero D.grading D.d D.d_mem hx p

/-- Multiplication on the right by a cycle commutes with the differential. -/
theorem d_mul_of_cycle {y : A} (hy : D.d y = 0) (x : A) :
    D.d (x * y) = D.d x * y := by
  induction x using DirectSum.Decomposition.inductionOn D.grading with
  | zero => simp
  | homogeneous x => simp [D.leibniz _ x.property y, hy]
  | add x x' hx hx' => simp [add_mul, map_add, hx, hx']

/-- Products of cycles are cycles. -/
theorem d_mul_eq_zero {x y : A} (hx : D.d x = 0) (hy : D.d y = 0) :
    D.d (x * y) = 0 := by
  rw [D.d_mul_of_cycle hy, hx, zero_mul]

/-- The subalgebra of cycles. -/
def cycles : Subalgebra R A where
  carrier := {x | D.d x = 0}
  mul_mem' := D.d_mul_eq_zero
  add_mem' := by intro x y hx hy; simp_all
  algebraMap_mem' := D.d_algebraMap

@[simp] theorem mem_cycles (x : A) : x ∈ D.cycles ↔ D.d x = 0 := Iff.rfl

/-- The differential with its codomain restricted to cycles, using `d_squared`. -/
def toCycles : A →ₗ[R] D.cycles :=
  D.d.codRestrict D.cycles.toSubmodule D.d_squared

@[simp] theorem coe_toCycles (x : A) : (D.toCycles x : A) = D.d x := rfl

/-- Boundaries as a submodule of the cycle algebra. -/
def boundaries : Submodule R D.cycles := LinearMap.range D.toCycles

/-- Membership in the boundary submodule is exactly the existence of a preimage under `d`. -/
@[simp] theorem mem_boundaries (x : D.cycles) :
    x ∈ D.boundaries ↔ ∃ y : A, D.d y = (x : A) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

/-- A cycle times a boundary is a boundary, including for inhomogeneous cycles. -/
theorem cycle_mul_boundary {x : A} (hx : D.d x = 0) (y : A) :
    ∃ z : A, D.d z = x * D.d y := by
  apply Grading.homogeneous_cycle_induction D.grading D.d D.d_mem
    (P := fun x => ∃ z : A, D.d z = x * D.d y) ?_ ?_ ?_ hx
  · exact ⟨0, by simp⟩
  · rintro x x' ⟨z, hz⟩ ⟨z', hz'⟩
    exact ⟨z + z', by simp [map_add, hz, hz', add_mul]⟩
  · intro p x hp hdx
    refine ⟨(p.negOnePow : ℤ) • (x * y), ?_⟩
    rw [map_zsmul, D.leibniz p hp y, hdx, zero_mul, zero_add, smul_smul]
    have hs : (p.negOnePow : ℤ) * (p.negOnePow : ℤ) = 1 :=
      congrArg Units.val (Int.units_mul_self p.negOnePow)
    rw [hs, one_smul]

/-- Boundaries absorb multiplication by a cycle on the left. -/
theorem boundaries_mul_left (a : D.cycles) {b : D.cycles} (hb : b ∈ D.boundaries) :
    a * b ∈ D.boundaries := by
  obtain ⟨y, hy⟩ := (D.mem_boundaries b).mp hb
  apply (D.mem_boundaries (a * b)).mpr
  change ∃ z : A, D.d z = (a : A) * (b : A)
  simpa only [hy] using D.cycle_mul_boundary a.property y

/-- Boundaries absorb multiplication by a cycle on the right. -/
theorem boundaries_mul_right (a : D.cycles) {b : D.cycles} (hb : b ∈ D.boundaries) :
    b * a ∈ D.boundaries := by
  obtain ⟨y, hy⟩ := (D.mem_boundaries b).mp hb
  apply (D.mem_boundaries (b * a)).mpr
  exact ⟨y * (a : A), by rw [D.d_mul_of_cycle a.property, hy]; rfl⟩

/-- The total homology algebra: cycles modulo boundaries.

The `Ring` and `Algebra R` instances are supplied by the two-sided-ideal quotient.
-/
abbrev Homology :=
  Quotient.Homology D.boundaries D.boundaries_mul_left D.boundaries_mul_right

/-- Explicit witness that the homology of any DGA is an algebra over its coefficient ring. -/
abbrev homologyAlgebra : Algebra R D.Homology := inferInstance

/-- The canonical algebra homomorphism from cycles to homology. -/
def homologyClass : D.cycles →ₐ[R] D.Homology :=
  Quotient.mk D.boundaries D.boundaries_mul_left D.boundaries_mul_right

theorem homologyClass_surjective : Function.Surjective D.homologyClass :=
  Quotient.mk_surjective D.boundaries D.boundaries_mul_left D.boundaries_mul_right

/-- A homology class is zero if and only if its representative is a boundary. -/
@[simp] theorem homologyClass_eq_zero_iff (x : D.cycles) :
    D.homologyClass x = 0 ↔ ∃ y : A, D.d y = (x : A) := by
  rw [homologyClass, Quotient.mk_eq_zero_iff, D.mem_boundaries]

/-- Equality of homology classes is equality of cycles modulo boundaries. -/
theorem homologyClass_eq_iff (x y : D.cycles) :
    D.homologyClass x = D.homologyClass y ↔ ∃ z : A, D.d z = (x : A) - (y : A) := by
  rw [homologyClass, Quotient.mk_eq_mk_iff, D.mem_boundaries]
  rfl

/-- Multiplication in homology is represented by multiplication of cycles. -/
@[simp] theorem homologyClass_mul (x y : D.cycles) :
    D.homologyClass (x * y) = D.homologyClass x * D.homologyClass y :=
  map_mul _ _ _

/-- The underlying module of the homology algebra is the usual cycle/boundary quotient. -/
def homologyModuleEquiv : D.Homology ≃ₗ[R] D.cycles ⧸ D.boundaries :=
  Quotient.quotientModuleEquiv D.boundaries D.boundaries_mul_left D.boundaries_mul_right

@[simp] theorem homologyModuleEquiv_class (x : D.cycles) :
    D.homologyModuleEquiv (D.homologyClass x) = D.boundaries.mkQ x :=
  Quotient.quotientModuleEquiv_mk D.boundaries D.boundaries_mul_left D.boundaries_mul_right x

end DGA
