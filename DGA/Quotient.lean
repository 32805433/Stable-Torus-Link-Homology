import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Algebra quotients by boundary submodules

If a submodule of an algebra is stable under multiplication on both sides, its
additive quotient inherits a ring and an algebra structure. This is the quotient
construction used for the total homology algebra of a differential graded algebra:
the ambient algebra here is its algebra of cycles.
-/

namespace DGA.Quotient

universe u v

variable {R : Type u} [CommRing R] {A : Type v} [Ring A] [Algebra R A]
variable {Z : Subalgebra R A} (B : Submodule R Z)
variable (hleft : ∀ (a : Z) {b : Z}, b ∈ B → a * b ∈ B)
variable (hright : ∀ (a : Z) {b : Z}, b ∈ B → b * a ∈ B)

/-- A boundary submodule stable under multiplication by cycles on both sides is
a two-sided ideal of the cycle algebra. -/
def boundariesIdeal : TwoSidedIdeal Z :=
  TwoSidedIdeal.mk' (B : Set Z) B.zero_mem
    (fun hx hy => B.add_mem hx hy) (fun hx => B.neg_mem hx)
    (fun {a _} hb => hleft a hb) (fun {_ b} ha => hright b ha)

@[simp]
theorem mem_boundariesIdeal (a : Z) :
    a ∈ boundariesIdeal B hleft hright ↔ a ∈ B := by
  simp [boundariesIdeal]

/-- The quotient of cycles by boundaries, with its inherited ring and
`R`-algebra structures. -/
abbrev Homology := (boundariesIdeal B hleft hright).ringCon.Quotient

/-- The canonical algebra homomorphism sending a cycle to its homology class. -/
def mk : Z →ₐ[R] Homology B hleft hright :=
  (boundariesIdeal B hleft hright).ringCon.mkₐ R

theorem mk_surjective : Function.Surjective (mk B hleft hright) :=
  RingCon.mkₐ_surjective _

/-- Two cycles represent the same class exactly when their difference is a boundary. -/
theorem mk_eq_mk_iff (a b : Z) :
    mk B hleft hright a = mk B hleft hright b ↔ a - b ∈ B := by
  exact (boundariesIdeal B hleft hright).ringCon.eq

/-- A cycle represents zero exactly when it is a boundary. -/
@[simp]
theorem mk_eq_zero_iff (a : Z) :
    mk B hleft hright a = 0 ↔ a ∈ B := by
  rw [← map_zero (mk B hleft hright), mk_eq_mk_iff]
  simp

@[simp]
theorem mk_mul (a b : Z) :
    mk B hleft hright (a * b) = mk B hleft hright a * mk B hleft hright b :=
  map_mul _ _ _

@[simp]
theorem mk_add (a b : Z) :
    mk B hleft hright (a + b) = mk B hleft hright a + mk B hleft hright b :=
  map_add _ _ _

@[simp]
theorem mk_smul (r : R) (a : Z) :
    mk B hleft hright (r • a) = r • mk B hleft hright a :=
  map_smul _ _ _

@[simp]
theorem mk_algebraMap (r : R) :
    mk B hleft hright (algebraMap R Z r) = algebraMap R (Homology B hleft hright) r :=
  AlgHom.commutes _ _

/-- The underlying module of the homology algebra is the ordinary quotient
module of cycles by boundaries. -/
def quotientModuleEquiv : Homology B hleft hright ≃ₗ[R] Z ⧸ B :=
  { _root_.Quotient.congrRight (fun _ _ => B.quotientRel_def.symm) with
    map_add' := by
      intro x y
      induction x using _root_.Quotient.inductionOn with
      | h a =>
        induction y using _root_.Quotient.inductionOn with
        | h b => rfl
    map_smul' := by
      intro r x
      induction x using _root_.Quotient.inductionOn with
      | h a => rfl }

@[simp]
theorem quotientModuleEquiv_mk (a : Z) :
    quotientModuleEquiv B hleft hright (mk B hleft hright a) = B.mkQ a :=
  rfl

end DGA.Quotient
