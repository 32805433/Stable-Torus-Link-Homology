import TorusLinkHomology.Generation.DenominatorDescent
import DGA.ExteriorPiBaseChange

/-!
# Exterior-algebra coordinates and denominator descent

A matrix and its adjugate clear each exterior-algebra coordinate by a power
of the determinant, with exponent equal to the size of the basis index.
Two relatively prime determinants then give integral coordinates in the
finite-adjugate proof of UEI-009.
-/

namespace TorusLinkHomology.Generation

variable {R : Type*} [CommRing R]

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Uniform scaling acts on the exterior basis vector indexed by `s` by the
power whose exponent is the size of `s`. -/
theorem exteriorAlgebra_map_smul_id_basis (a : R) (s : Finset ι) :
    ExteriorAlgebra.map (a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R)))
      ((Pi.basisFun R ι).ExteriorAlgebra s) =
      a ^ s.card • (Pi.basisFun R ι).ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.map_apply_ιMulti,
    LinearMap.smul_apply, LinearMap.id_apply, Function.comp_def]
  rw [AlternatingMap.map_smul_univ]
  simp

/-- The corresponding formula on arbitrary exterior coordinates. -/
theorem exteriorAlgebra_map_smul_id_coordinate (a : R)
    (w : ExteriorAlgebra R (ι → R)) (s : Finset ι) :
    (Pi.basisFun R ι).ExteriorAlgebra.repr
      (ExteriorAlgebra.map (a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R))) w) s =
      a ^ s.card * (Pi.basisFun R ι).ExteriorAlgebra.repr w s := by
  classical
  let b := (Pi.basisFun R ι).ExteriorAlgebra
  conv_lhs => rw [← b.sum_repr w]
  dsimp only [b]
  simp only [map_sum, map_smul, exteriorAlgebra_map_smul_id_basis,
    Module.Basis.repr_self]
  simp [Finsupp.single_apply, mul_comm]

/-- The adjugate clears each full exterior-algebra coordinate, with exponent
the cardinality of the indexing set. -/
theorem exteriorAlgebra_adjugate_coordinate (B : Matrix ι ι R)
    (w : ExteriorAlgebra R (ι → R)) (s : Finset ι) :
    B.det ^ s.card * (Pi.basisFun R ι).ExteriorAlgebra.repr w s =
      (Pi.basisFun R ι).ExteriorAlgebra.repr
        (ExteriorAlgebra.map B.adjugate.toLin' (ExteriorAlgebra.map B.toLin' w)) s := by
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, ← Matrix.toLin'_mul,
    Matrix.adjugate_mul, map_smul, Matrix.toLin'_one]
  exact (exteriorAlgebra_map_smul_id_coordinate B.det w s).symm

variable {S : Type*} [CommRing S] [Algebra R S]

/-- A matrix over the original ring preserves integrality of all full exterior
coordinates after extension of scalars. -/
theorem isInteger_exteriorAlgebra_map_coordinate (B : Matrix ι ι R)
    (w : ExteriorAlgebra S (ι → S))
    (hw : ∀ t, IsLocalization.IsInteger R ((Pi.basisFun S ι).ExteriorAlgebra.repr w t))
    (s : Finset ι) :
    IsLocalization.IsInteger R ((Pi.basisFun S ι).ExteriorAlgebra.repr
      (ExteriorAlgebra.map (B.map (algebraMap R S)).toLin' w) s) := by
  obtain ⟨v, rfl⟩ := (ExteriorAlgebra.exists_piBaseChange_eq_iff (algebraMap R S) w).mpr hw
  rw [← ExteriorAlgebra.piBaseChange_map_matrix, ExteriorAlgebra.repr_piBaseChange]
  exact ⟨_, rfl⟩

/-- The size of a basis index is the exponent sufficient to clear that
coordinate using the determinant. -/
theorem isInteger_exteriorAlgebra_det_coordinate (B : Matrix ι ι R)
    (w : ExteriorAlgebra S (ι → S))
    (hw : ∀ t, IsLocalization.IsInteger R ((Pi.basisFun S ι).ExteriorAlgebra.repr
      (ExteriorAlgebra.map (B.map (algebraMap R S)).toLin' w) t)) (s : Finset ι) :
    IsLocalization.IsInteger R
      (algebraMap R S (B.det ^ s.card) * (Pi.basisFun S ι).ExteriorAlgebra.repr w s) := by
  rw [map_pow, (algebraMap R S).map_det]
  change IsLocalization.IsInteger R
    ((B.map (algebraMap R S)).det ^ s.card * (Pi.basisFun S ι).ExteriorAlgebra.repr w s)
  rw [exteriorAlgebra_adjugate_coordinate]
  simpa only [← RingHom.mapMatrix_apply, RingHom.map_adjugate] using
    isInteger_exteriorAlgebra_map_coordinate B.adjugate
      (ExteriorAlgebra.map (B.map (algebraMap R S)).toLin' w) hw s

variable {F : Type*} [IsDomain R] [UniqueFactorizationMonoid R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The full exterior-algebra form of two-minor denominator descent. -/
theorem isInteger_exteriorAlgebra_coordinate_of_isRelPrime_dets
    (B C : Matrix ι ι R) (hBC : IsRelPrime B.det C.det)
    (w : ExteriorAlgebra F (ι → F))
    (hB : ∀ t, IsLocalization.IsInteger R ((Pi.basisFun F ι).ExteriorAlgebra.repr
      (ExteriorAlgebra.map (B.map (algebraMap R F)).toLin' w) t))
    (hC : ∀ t, IsLocalization.IsInteger R ((Pi.basisFun F ι).ExteriorAlgebra.repr
      (ExteriorAlgebra.map (C.map (algebraMap R F)).toLin' w) t)) (s : Finset ι) :
    IsLocalization.IsInteger R ((Pi.basisFun F ι).ExteriorAlgebra.repr w s) :=
  isInteger_of_isRelPrime_pow_mul hBC s.card s.card
    (isInteger_exteriorAlgebra_det_coordinate B w hB s)
    (isInteger_exteriorAlgebra_det_coordinate C w hC s)

end TorusLinkHomology.Generation
