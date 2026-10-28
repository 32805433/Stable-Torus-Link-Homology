import TorusLinkHomology.Generation.AuxiliaryStatement
import TorusLinkHomology.Generation.CoordinateContraction
import DGA.ExteriorMap
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The zero-offset auxiliary coefficient complex

Euler's recurrence expresses the first `r` coefficients of `E^N` as an
invertible triangular combination of the coordinate variables. The induced
exterior change of generators transports the coordinate Koszul contraction.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientComplex

/-- The triangular change from auxiliary odd generators to coordinate odd
generators. Rows index coordinates and columns index the coefficients `G_{j+1}`. -/
def zeroOffsetMatrix (N r : ℕ) : Matrix (Fin r) (Fin r) (R r) :=
  fun i j => if i ≤ j then
    invNat r (j.val + 1) *
      ((((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - ((j.val + 1 : ℕ) : R r)) *
        G N r (j.val - i.val))
  else 0

theorem zeroOffsetMatrix_upperTriangular (N r : ℕ) :
    (zeroOffsetMatrix N r).IsUpperTriangular := by
  intro i j hij
  exact if_neg (not_le.mpr hij)

@[simp] theorem zeroOffsetMatrix_diag (N r : ℕ) (i : Fin r) :
    zeroOffsetMatrix N r i i = (N : R r) := by
  simp only [zeroOffsetMatrix, le_refl, ↓reduceIte, Nat.sub_self, G_zero, mul_one]
  have he : (((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) -
      ((i.val + 1 : ℕ) : R r)) = (N : R r) * ((i.val + 1 : ℕ) : R r) := by
    push_cast
    ring
  rw [he, mul_left_comm, invNat_mul_nat _ _ (by omega), mul_one]

/-- The determinant is the nonzero rational scalar `N^r`. -/
theorem zeroOffsetMatrix_det (N r : ℕ) :
    (zeroOffsetMatrix N r).det = (N : R r) ^ r := by
  rw [Matrix.det_of_isUpperTriangular (zeroOffsetMatrix_upperTriangular N r)]
  simp

theorem zeroOffsetMatrix_det_isUnit (N r : ℕ) (hN : 0 < N) :
    IsUnit (zeroOffsetMatrix N r).det := by
  rw [zeroOffsetMatrix_det]
  have h : IsUnit (N : ℚ) := (by exact_mod_cast Nat.ne_of_gt hN : (N : ℚ) ≠ 0).isUnit
  have h' : IsUnit (N : R r) := by simpa using h.map (algebraMap ℚ (R r))
  exact h'.pow r

/-- The Euler matrix expresses `G_{j+1}` in the coordinate variables. -/
theorem zeroOffsetMatrix_coordinates (N r : ℕ) (j : Fin r) :
    (∑ i : Fin r, zeroOffsetMatrix N r i j * e r i) = G N r (j.val + 1) := by
  classical
  calc
    _ = invNat r (j.val + 1) *
        (∑ i : Fin r, if i.val + 1 ≤ j.val + 1 then
          (((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - ((j.val + 1 : ℕ) : R r)) *
            e r i * G N r (j.val + 1 - (i.val + 1)) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ≤ j
      · have hi' : i.val + 1 ≤ j.val + 1 := Nat.add_le_add_right hi 1
        rw [zeroOffsetMatrix, if_pos hi, if_pos hi', Nat.add_sub_add_right]
        ring
      · have hi' : ¬ i.val + 1 ≤ j.val + 1 := by omega
        rw [zeroOffsetMatrix, if_neg hi, if_neg hi', zero_mul, mul_zero]
    _ = _ := by
      rw [← coefficient_recurrence_guarded, ← mul_assoc,
        invNat_mul_nat _ _ (by omega), one_mul]

/-- The invertible triangular change of odd-generator modules. -/
def zeroOffsetVectorEquiv (N r : ℕ) (hN : 0 < N) : V r ≃ₗ[R r] V r :=
  Matrix.toLinearEquiv
    (Finsupp.basisSingleOne : Module.Basis (Fin r) (R r) (V r))
    (zeroOffsetMatrix N r) (zeroOffsetMatrix_det_isUnit N r hN)

@[simp] theorem zeroOffsetVectorEquiv_single (N r : ℕ) (hN : 0 < N) (j : Fin r) :
    zeroOffsetVectorEquiv N r hN (Finsupp.single j (1 : R r)) =
      ∑ i : Fin r, zeroOffsetMatrix N r i j • Finsupp.single i (1 : R r) := by
  exact Matrix.toLin_self _ _ _ j

/-- Pulling back the coordinate functional gives the auxiliary coefficient functional. -/
theorem zeroOffset_functional (N r : ℕ) (hN : 0 < N) :
    (TorusLinkHomology.differentialFunctional 1 r).comp
      (zeroOffsetVectorEquiv N r hN).toLinearMap = differentialFunctional N r 0 := by
  apply (Finsupp.basisSingleOne : Module.Basis (Fin r) (R r) (V r)).ext
  intro j
  change TorusLinkHomology.differentialFunctional 1 r
    (zeroOffsetVectorEquiv N r hN (Finsupp.single j 1)) =
      differentialFunctional N r 0 (Finsupp.single j 1)
  rw [zeroOffsetVectorEquiv_single, map_sum]
  simp only [map_smul, TorusLinkHomology.differentialFunctional, differentialFunctional,
    Finsupp.linearCombination_single,
    CoordinateKoszul.differentialCoefficient_one, TorusLinkHomology.u,
    Nat.zero_add, smul_eq_mul, one_mul]
  exact zeroOffsetMatrix_coordinates N r j

/-- An algebra equivalence from the zero-offset auxiliary complex to the
coordinate Koszul complex, fixing every polynomial coefficient. -/
def zeroOffsetChainEquiv (N r : ℕ) (hN : 0 < N) : A r ≃ₐ[R r] A r :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map (zeroOffsetVectorEquiv N r hN).toLinearMap)
    (ExteriorAlgebra.map (zeroOffsetVectorEquiv N r hN).symm.toLinearMap)
    (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.comp_symm, ExteriorAlgebra.map_id])
    (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.symm_comp, ExteriorAlgebra.map_id])

/-- The triangular algebra equivalence intertwines the two differentials. -/
theorem zeroOffsetChainEquiv_d (N r : ℕ) (hN : 0 < N) (x : A r) :
    TorusLinkHomology.d 1 r (zeroOffsetChainEquiv N r hN x) =
      zeroOffsetChainEquiv N r hN (d N r 0 x) := by
  exact ExteriorAlgebra.contractLeft_map_of_comp_eq
    (zeroOffsetVectorEquiv N r hN).toLinearMap
    (TorusLinkHomology.differentialFunctional 1 r) (differentialFunctional N r 0)
    (zeroOffset_functional N r hN) x

/-- Every zero-offset auxiliary cycle is a rational scalar plus a boundary. -/
theorem zeroOffset_cycle_eq_scalar_add_boundary (N r : ℕ) (hN : 0 < N)
    (x : A r) (hx : d N r 0 x = 0) :
    ∃ q : ℚ, ∃ b : A r, x = q • (1 : A r) + d N r 0 b := by
  have hz : TorusLinkHomology.d 1 r (zeroOffsetChainEquiv N r hN x) = 0 := by
    rw [zeroOffsetChainEquiv_d, hx, map_zero]
  obtain ⟨q, b, hb⟩ := CoordinateKoszul.cycle_eq_scalar_add_boundary r
    (zeroOffsetChainEquiv N r hN x) hz
  refine ⟨q, (zeroOffsetChainEquiv N r hN).symm b, ?_⟩
  apply (zeroOffsetChainEquiv N r hN).injective
  rw [map_add, map_rat_smul, map_one, ← zeroOffsetChainEquiv_d,
    AlgEquiv.apply_symm_apply]
  exact hb

/-- The offset-zero induction base: the scalar subalgebra already represents
all homology classes, so in particular the designated tail subalgebra does. -/
theorem tailGeneration_zero_offset (N r : ℕ) (hN : 0 < N) : TailGeneration N r 0 := by
  intro x hx
  obtain ⟨q, b, hb⟩ := zeroOffset_cycle_eq_scalar_add_boundary N r hN x hx
  refine ⟨q • (1 : A r), ?_, b, hb⟩
  rw [← IsScalarTower.algebraMap_smul (R r)]
  exact (tailSubalgebra N r 0).smul_mem (Subalgebra.one_mem _) _

end TorusLinkHomology.CoefficientComplex
