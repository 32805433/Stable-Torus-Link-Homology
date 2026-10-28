import DGA.ExteriorScalarChange
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-! # Scalar extension in the standard finite exterior basis -/

noncomputable section

namespace ExteriorAlgebra

variable {R S ι : Type*} [CommRing R] [CommRing S]

/-- Apply a coefficient homomorphism to a finite coordinate vector. -/
def piScalarMap (f : R →+* S) : (ι → R) →ₛₗ[f] (ι → S) where
  toFun v i := f (v i)
  map_add' v w := by ext i; exact map_add f _ _
  map_smul' r v := by ext i; exact map_mul f _ _

@[simp] theorem piScalarMap_apply (f : R →+* S) (v : ι → R) (i : ι) :
    piScalarMap f v i = f (v i) := rfl

@[simp] theorem piScalarMap_basis [Fintype ι] [DecidableEq ι] (f : R →+* S) (i : ι) :
    piScalarMap f (Pi.basisFun R ι i) = Pi.basisFun S ι i := by
  ext j
  by_cases h : i = j <;> simp [Pi.basisFun_apply, h]

/-- Scalar extension of the full exterior algebra in coordinate form. -/
def piBaseChange (f : R →+* S) :
    ExteriorAlgebra R (ι → R) →+* ExteriorAlgebra S (ι → S) :=
  mapOfSemilinear f (piScalarMap f)

@[simp] theorem piBaseChange_iota (f : R →+* S) (v : ι → R) :
    piBaseChange f (ExteriorAlgebra.ι R v) = ExteriorAlgebra.ι S (piScalarMap f v) :=
  mapOfSemilinear_iota _ _ _

theorem piBaseChange_smul (f : R →+* S) (r : R)
    (x : ExteriorAlgebra R (ι → R)) :
    piBaseChange f (r • x) = f r • piBaseChange f x :=
  mapOfSemilinear_smul _ _ _ _

variable [Fintype ι] [LinearOrder ι]

@[simp] theorem piBaseChange_basis (f : R →+* S) (s : Finset ι) :
    piBaseChange f ((Pi.basisFun R ι).ExteriorAlgebra s) =
      (Pi.basisFun S ι).ExteriorAlgebra s := by
  simp only [basis_apply, ιMulti_family, ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, piBaseChange_iota, piScalarMap_basis]

/-- Scalar extension applies the coefficient map to each exterior coordinate. -/
@[simp] theorem repr_piBaseChange (f : R →+* S)
    (x : ExteriorAlgebra R (ι → R)) (s : Finset ι) :
    (Pi.basisFun S ι).ExteriorAlgebra.repr (piBaseChange f x) s =
      f ((Pi.basisFun R ι).ExteriorAlgebra.repr x s) := by
  classical
  conv_lhs => rw [← (Pi.basisFun R ι).ExteriorAlgebra.sum_repr x]
  simp only [map_sum, piBaseChange_smul, piBaseChange_basis, map_smul,
    Module.Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]
  simp

theorem piBaseChange_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (piBaseChange f :
      ExteriorAlgebra R (ι → R) → ExteriorAlgebra S (ι → S)) := by
  intro x y hxy
  apply (Pi.basisFun R ι).ExteriorAlgebra.repr.injective
  ext s
  apply hf
  simpa using congrArg (fun z => (Pi.basisFun S ι).ExteriorAlgebra.repr z s) hxy

/-- A vector descends exactly when all its standard exterior coordinates do. -/
theorem exists_piBaseChange_eq_iff (f : R →+* S)
    (y : ExteriorAlgebra S (ι → S)) :
    (∃ x : ExteriorAlgebra R (ι → R), piBaseChange f x = y) ↔
      ∀ s : Finset ι, ∃ r : R, f r = (Pi.basisFun S ι).ExteriorAlgebra.repr y s := by
  classical
  constructor
  · rintro ⟨x, rfl⟩ s
    exact ⟨_, (repr_piBaseChange f x s).symm⟩
  · intro h
    choose c hc using h
    refine ⟨∑ s : Finset ι, c s • (Pi.basisFun R ι).ExteriorAlgebra s, ?_⟩
    apply (Pi.basisFun S ι).ExteriorAlgebra.repr.injective
    ext s
    simp [repr_piBaseChange, Finsupp.finsetSum_apply, Finsupp.single_apply, apply_ite, hc]

/-- Matrix application commutes with extension of its coefficients. -/
theorem piScalarMap_matrix (f : R →+* S) (B : Matrix ι ι R) (v : ι → R) :
    piScalarMap f (B.toLin' v) = (B.map f).toLin' (piScalarMap f v) := by
  ext i
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum]

/-- Naturality of the full exterior matrix action under scalar extension. -/
theorem piBaseChange_map_matrix (f : R →+* S) (B : Matrix ι ι R)
    (x : ExteriorAlgebra R (ι → R)) :
    piBaseChange f (map B.toLin' x) =
      map (B.map f).toLin' (piBaseChange f x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [AlgHom.commutes, piBaseChange, mapOfSemilinear_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    simp only [map_mul, map_apply_ι, piBaseChange_iota, piScalarMap_matrix, hx]

end ExteriorAlgebra
