import TorusLinkHomology.Generation.ShortRange
import DGA.ExteriorMap

/-! # The original Koszul complex in finite function coordinates -/

noncomputable section

namespace TorusLinkHomology.PiCoordinates

abbrev PiA (n : ℕ) := ExteriorAlgebra (R n) (Fin n → R n)

/-- The standard identification of finitely supported vectors with functions. -/
def vectorEquiv (n : ℕ) : V n ≃ₗ[R n] (Fin n → R n) :=
  Finsupp.linearEquivFunOnFinite (R n) (R n) (Fin n)

/-- The induced equivalence of exterior algebras, over the original coefficient ring. -/
def toPi (n : ℕ) : A n ≃ₐ[R n] PiA n :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map (vectorEquiv n).toLinearMap)
    (ExteriorAlgebra.map (vectorEquiv n).symm.toLinearMap)
    (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.comp_symm, ExteriorAlgebra.map_id])
    (by rw [ExteriorAlgebra.map_comp_map, LinearEquiv.symm_comp, ExteriorAlgebra.map_id])

@[simp] theorem toPi_iota (n : ℕ) (v : V n) :
    toPi n (ExteriorAlgebra.ι (R n) v) =
      ExteriorAlgebra.ι (R n) (vectorEquiv n v) :=
  ExteriorAlgebra.map_apply_ι _ _

@[simp] theorem toPi_xi (n : ℕ) (i : Fin n) :
    toPi n (xi n i) = ExteriorAlgebra.ι (R n) (Pi.basisFun (R n) (Fin n) i) := by
  simp [xi, vectorEquiv, Pi.basisFun_apply]

/-- The differential functional transported to finite function coordinates. -/
def functional (N n : ℕ) : Module.Dual (R n) (Fin n → R n) :=
  (differentialFunctional N n).comp (vectorEquiv n).symm.toLinearMap

@[simp] theorem functional_basis (N n : ℕ) (i : Fin n) :
    functional N n (Pi.basisFun (R n) (Fin n) i) = differentialCoefficient N n i := by
  simp [functional, vectorEquiv, Pi.basisFun_apply, differentialFunctional]

theorem functional_apply (N n : ℕ) (v : Fin n → R n) :
    functional N n v = ∑ i : Fin n, differentialCoefficient N n i * v i := by
  conv_lhs => rw [← (Pi.basisFun (R n) (Fin n)).sum_repr v]
  simp only [map_sum, map_smul, functional_basis, Pi.basisFun_repr, smul_eq_mul, mul_comm]

def piDifferential (N n : ℕ) : PiA n →ₗ[R n] PiA n :=
  CliffordAlgebra.contractLeft (Q := 0) (functional N n)

/-- The coordinate change commutes with the differential on every chain. -/
theorem toPi_d (N n : ℕ) (x : A n) :
    toPi n (d N n x) = piDifferential N n (toPi n x) := by
  symm
  apply ExteriorAlgebra.contractLeft_map_of_comp_eq
  simp only [functional, LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.comp_id]

/-- The columns used in the minor calculation are the actual named cycles. -/
theorem toPi_mu (N a : ℕ) (j : Fin a) :
    toPi (a + 1) (mu N (a + 1) (j.val + 1)) =
      ExteriorAlgebra.ι (R (a + 1)) (fun i => Generation.muMatrix N a i j) := by
  rw [Generation.mu_eq_sum_muMatrix, map_sum]
  simp only [map_smul, toPi_xi]
  simp only [← map_smul, ← map_sum]
  congr 1
  exact (Pi.basisFun (R (a + 1)) (Fin (a + 1))).sum_repr
    (fun i => Generation.muMatrix N a i j)

end TorusLinkHomology.PiCoordinates
