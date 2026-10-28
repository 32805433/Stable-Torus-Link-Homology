import TorusLinkHomology.Generation.Connecting
import DGA.ExteriorProducts

/-!
# Explicit comparison coordinates and connecting representatives

The distinguished new generator is the normalized last generator after
subtracting its common-coordinate part. Only rational scalars are inverted.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientComplex

/-- The rational normalization `L/m` from the comparison coordinate change. -/
def comparisonNormalization (N r ell : ℕ) : R (r + 1) :=
  ((ell + r + 2 : ℕ) : R (r + 1)) * invNat (r + 1) (N * (r + 1) - (ell + 1))

/-- The generator eta-prime of CI-06, with the common part written using
the coordinate projection and the inverse rotation. -/
def etaPrime (N r ell : ℕ) : A (r + 1) :=
  comparisonNormalization N r ell •
    (xi (r + 1) (Fin.last r) -
      ExteriorAlgebra.map (rotateCoordinates r).symm.toLinearMap
        (commonProjection r (tail N (r + 1) ell (ell + r + 2))))

/-- The underlying degree-one vector of the changed distinguished generator. -/
def etaPrimeVector (N r ell : ℕ) : V (r + 1) :=
  comparisonNormalization N r ell •
    (Finsupp.single (Fin.last r) 1 - (rotateCoordinates r).symm
      (ExteriorAlgebra.contractionProjection (firstCoordinate r) (firstVector r)
        (tailVector N (r + 1) ell (ell + r + 2))))

@[simp] theorem iota_etaPrimeVector (N r ell : ℕ) :
    ExteriorAlgebra.ι (R (r + 1)) (etaPrimeVector N r ell) = etaPrime N r ell := by
  rw [etaPrime, ← iota_tailVector N (r + 1) ell (ell + r + 2), commonProjection,
    ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι]
  simp [etaPrimeVector, xi]

theorem etaPrime_sq_zero (N r ell : ℕ) : etaPrime N r ell * etaPrime N r ell = 0 := by
  rw [← iota_etaPrimeVector]
  exact ExteriorAlgebra.ι_sq_zero _

theorem J_rotateInverse_commonProjection (N r ell : ℕ) (a : A (r + 1)) :
    J N (r + 1) (ell + 1)
      (ExteriorAlgebra.map (rotateCoordinates r).symm.toLinearMap (commonProjection r a)) =
        commonProjection r a := by
  rw [J_factorization]
  have hrot : Function.LeftInverse (ExteriorAlgebra.map (rotateCoordinates r).toLinearMap)
      (ExteriorAlgebra.map (rotateCoordinates r).symm.toLinearMap) :=
    ExteriorAlgebra.leftInverse_map_iff.mpr (rotateCoordinates r).apply_symm_apply
  rw [hrot]
  rw [ExteriorAlgebra.map_replaceCoordinate]
  have hzero : CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r)
      (commonProjection r a) = 0 :=
    ExteriorAlgebra.contractLeft_projection _ _ (firstCoordinate_firstVector r) a
  rw [hzero, mul_zero, sub_zero]

/-- The comparison sends eta-prime to the final coefficient times the old
distinguished generator. -/
theorem J_etaPrime (N r ell : ℕ) (hm : ell + 1 < N * (r + 1)) :
    J N (r + 1) (ell + 1) (etaPrime N r ell) =
      e (r + 1) (Fin.last r) • xi (r + 1) 0 := by
  rw [etaPrime, map_smul, map_sub, J_xi, J_rotateInverse_commonProjection]
  have hind : ell + 1 + (Fin.last r).val + 1 = ell + r + 2 := by simp; omega
  rw [Nat.add_sub_cancel_right, hind]
  have hpart : tail N (r + 1) ell (ell + r + 2) -
      commonProjection r (tail N (r + 1) ell (ell + r + 2)) =
        firstCoordinate r (tailVector N (r + 1) ell (ell + r + 2)) • xi (r + 1) 0 := by
    rw [commonProjection, ExteriorAlgebra.map_contractionProjection, sub_sub_cancel]
    rw [← iota_tailVector N (r + 1) ell (ell + r + 2), CliffordAlgebra.contractLeft_ι]
    change xi (r + 1) 0 * algebraMap (R (r + 1)) (A (r + 1)) _ = _
    rw [Algebra.smul_def, Algebra.commutes]
  rw [hpart, smul_smul, comparisonNormalization, boundary_coefficient_rescale N r ell hm]

/-- The differential of eta-prime is `t*f`. -/
theorem d_etaPrime (N r ell : ℕ) (hm : ell + 1 < N * (r + 1)) :
    d N (r + 1) (ell + 1) (etaPrime N r ell) =
      algebraMap (R (r + 1)) (A (r + 1))
        (e (r + 1) (Fin.last r) * G N (r + 1) (ell + 1)) := by
  apply J_injective N r ell hm
  rw [← d_J, Nat.add_sub_cancel_right, J_etaPrime N r ell hm, map_smul, d_xi,
    AlgHom.commutes]
  simp [Algebra.smul_def, map_mul]

/-- The distinguished new coordinate vanishes in the reduced complex. -/
theorem rhoSucc_etaPrime (N r ell : ℕ) (hm : ell + 1 < N * (r + 1)) :
    rhoSucc N r (ell + 1) (etaPrime N r ell) = 0 := by
  rw [← dropFirst_J, J_etaPrime N r ell hm, dropFirst_smul,
    reduceCoefficients_e_last, zero_smul]

/-- The explicit connecting expression associated with `d a = -t*b`. -/
def connectingOmega (N r ell : ℕ) (a b : A (r + 1)) : A (r + 1) :=
  G N (r + 1) (ell + 1) • a + etaPrime N r ell * b

/-- This is CI-12 before specializing to an ordered product. -/
theorem connectingOmega_represents (N r ell : ℕ) (hm : ell + 1 < N * (r + 1))
    (a b : A (r + 1))
    (hab : d N (r + 1) (ell + 1) a = -e (r + 1) (Fin.last r) • b) :
    ConnectingRepresentative N r ell (rhoSucc N r (ell + 1) a)
      (connectingOmega N r ell a b) := by
  refine ⟨xi (r + 1) 0 * J N (r + 1) (ell + 1) a, ?_, ?_⟩
  · rw [p_mul_J]
    have hp : p r (xi (r + 1) 0) = 1 := by
      rw [p, xi, CliffordAlgebra.contractLeft_ι, dropFirst_algebraMap]
      simp [firstCoordinate]
    rw [hp, one_mul]
  · rw [connectingOmega, map_add, map_smul, map_mul, J_etaPrime N r ell hm]
    change _ = CliffordAlgebra.contractLeft (Q := 0) (differentialFunctional N (r + 1) ell)
      (ExteriorAlgebra.ι (R (r + 1)) (Finsupp.single 0 1) * _)
    rw [CliffordAlgebra.contractLeft_ι_mul]
    have hfirst : differentialFunctional N (r + 1) ell (Finsupp.single 0 1) =
        G N (r + 1) (ell + 1) := by simp [differentialFunctional]
    rw [hfirst]
    change _ = G N (r + 1) (ell + 1) • J N (r + 1) (ell + 1) a -
      xi (r + 1) 0 * d N (r + 1) ell (J N (r + 1) (ell + 1) a)
    have hchain := d_J N (r + 1) (ell + 1) a
    simp only [Nat.add_sub_cancel_right] at hchain
    rw [hchain, hab, map_smul]
    simp only [neg_smul, mul_neg, sub_neg_eq_add, smul_mul_assoc, mul_smul_comm]

theorem connectingOmega_is_cycle (N r ell : ℕ) (hm : ell + 1 < N * (r + 1))
    (a b : A (r + 1))
    (hab : d N (r + 1) (ell + 1) a = -e (r + 1) (Fin.last r) • b) :
    d N (r + 1) (ell + 1) (connectingOmega N r ell a b) = 0 :=
  (connectingOmega_represents N r ell hm a b hab).is_cycle hm

/-- Signed deletion from an ordered list, retaining the original order in
every remaining product. -/
def connectingDeletion (r q : ℕ) (v : Fin (q + 1) → V (r + 1))
    (beta : Fin (q + 1) → R (r + 1)) : A (r + 1) :=
  ∑ i : Fin (q + 1), ((-1 : R (r + 1)) ^ i.val * beta i) •
    ExteriorAlgebra.ιMulti (R (r + 1)) q (v ∘ i.succAbove)

/-- The hypothesis on the degree-one factors gives exactly the signed
deletion differential used in the explicit connecting expression. -/
theorem d_ordered_product_eq (N r ell q : ℕ) (v : Fin (q + 1) → V (r + 1))
    (beta : Fin (q + 1) → R (r + 1))
    (hbeta : ∀ i, differentialFunctional N (r + 1) (ell + 1) (v i) =
      -e (r + 1) (Fin.last r) * beta i) :
    d N (r + 1) (ell + 1) (ExteriorAlgebra.ιMulti (R (r + 1)) (q + 1) v) =
      -e (r + 1) (Fin.last r) • connectingDeletion r q v beta := by
  change CliffordAlgebra.contractLeft (Q := 0) (differentialFunctional N (r + 1) (ell + 1)) _ = _
  rw [ExteriorAlgebra.contractLeft_ιMulti, connectingDeletion, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hbeta i, smul_smul]
  congr 1
  ring

/-- CI-12 for a nonempty ordered list of degree-one factors. -/
theorem connecting_ordered_product (N r ell q : ℕ)
    (hm : ell + 1 < N * (r + 1)) (v : Fin (q + 1) → V (r + 1))
    (beta : Fin (q + 1) → R (r + 1))
    (hbeta : ∀ i, differentialFunctional N (r + 1) (ell + 1) (v i) =
      -e (r + 1) (Fin.last r) * beta i) :
    ConnectingRepresentative N r ell
      (rhoSucc N r (ell + 1) (ExteriorAlgebra.ιMulti (R (r + 1)) (q + 1) v))
      (G N (r + 1) (ell + 1) • ExteriorAlgebra.ιMulti (R (r + 1)) (q + 1) v +
        etaPrime N r ell * connectingDeletion r q v beta) :=
  connectingOmega_represents N r ell hm _ _ (d_ordered_product_eq N r ell q v beta hbeta)

/-- The empty-product connecting class is represented by the missing equation. -/
theorem connecting_empty_product (N r ell : ℕ) :
    ConnectingRepresentative N r ell 1
      (algebraMap (R (r + 1)) (A (r + 1)) (G N (r + 1) (ell + 1))) := by
  refine ⟨xi (r + 1) 0, ?_, ?_⟩
  · rw [p, xi, CliffordAlgebra.contractLeft_ι, dropFirst_algebraMap]
    simp [firstCoordinate]
  · rw [AlgHom.commutes, d_xi]
    simp

end TorusLinkHomology.CoefficientComplex
