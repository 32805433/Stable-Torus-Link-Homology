import TorusLinkHomology.Generation.UniversalTransferBeta
import DGA.ExteriorProducts
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-! # The universal connecting cycle, before specialization -/

noncomputable section

namespace TorusLinkHomology.UniversalTransfer

open scoped BigOperators

def etaCoefficient (N m : ℕ) : R := MvPolynomial.C (-(N : ℚ) * (m : ℚ)⁻¹)
def etaPrime (N m : ℕ) : A := etaCoefficient N m • oddQ 0

theorem etaCoefficient_mul_qEquation (N m : ℕ) (hN : 0 < N) (hm : 0 < m) :
    etaCoefficient N m * qEquation N m 0 = y 0 * v 0 := by
  have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hscalar : etaCoefficient N m * MvPolynomial.C ((N : ℚ)⁻¹) * -(m : R) = 1 := by
    have hq : (-(N : ℚ) * (m : ℚ)⁻¹) * (N : ℚ)⁻¹ * -(m : ℚ) = 1 := by
      field_simp
    simpa only [etaCoefficient, map_mul, map_neg, map_natCast, map_one] using
      congrArg (MvPolynomial.C : ℚ →+* R) hq
  rw [qEquation_zero]
  calc
    _ = (etaCoefficient N m * MvPolynomial.C ((N : ℚ)⁻¹) * -(m : R)) * (y 0 * v 0) := by ring
    _ = _ := by rw [hscalar, one_mul]

theorem d_etaPrime (N m : ℕ) (hN : 0 < N) (hm : 0 < m) :
    d N m (etaPrime N m) = algebraMap R A (y 0 * v 0) := by
  rw [etaPrime, map_smul, d_oddQ, Algebra.smul_def, ← map_mul,
    etaCoefficient_mul_qEquation N m hN hm]

theorem d_etaPrime_mul (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (a : A) :
    d N m (etaPrime N m * a) = (y 0 * v 0) • a - etaPrime N m * d N m a := by
  rw [etaPrime, smul_mul_assoc, map_smul]
  change etaCoefficient N m •
    CliffordAlgebra.contractLeft (Q := 0) (functional N m)
      (ExteriorAlgebra.ι R (Finsupp.single (Sum.inr 0) 1) * a) = _
  rw [CliffordAlgebra.contractLeft_ι_mul]
  simp only [functional, Finsupp.linearCombination_single, one_smul, equation,
    smul_sub, smul_smul, etaCoefficient_mul_qEquation N m hN hm]
  rw [smul_mul_assoc]
  rfl

theorem functional_oddA_small (N m t : ℕ) (hN : t < N) (hm : t < m) :
    functional N m (Finsupp.single (Sum.inl t) 1) = -y 0 * beta N t := by
  simp only [functional, Finsupp.linearCombination_single, one_smul, equation,
    shiftedV, if_neg (by omega : ¬ m ≤ t), zero_sub, g_eq_y_mul_beta N t hN, neg_mul]

def orderedA (q : ℕ) (t : Fin q → ℕ) : A :=
  ExteriorAlgebra.ιMulti R q (fun i => Finsupp.single (Sum.inl (t i)) 1)

def betaDeletion (N q : ℕ) (t : Fin (q + 1) → ℕ) : A :=
  ∑ i : Fin (q + 1), ((-1 : R) ^ i.val * beta N (t i)) •
    orderedA q (t ∘ i.succAbove)

theorem d_orderedA (N m q : ℕ) (t : Fin (q + 1) → ℕ)
    (htN : ∀ i, t i < N) (htm : ∀ i, t i < m) :
    d N m (orderedA (q + 1) t) = -y 0 • betaDeletion N q t := by
  change CliffordAlgebra.contractLeft (Q := 0) (functional N m)
    (ExteriorAlgebra.ιMulti R (q + 1) _) = _
  rw [ExteriorAlgebra.contractLeft_ιMulti]
  unfold betaDeletion
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [functional_oddA_small N m (t i) (htN i) (htm i), smul_smul]
  change (((-1 : R) ^ i.val) * (-y 0 * beta N (t i))) •
      orderedA q (t ∘ i.succAbove) = _
  congr 1
  ring

theorem smul_injective (c : R) (hc : c ≠ 0) : Function.Injective (fun a : A => c • a) := by
  let : LinearOrder (ℕ ⊕ ℕ) := Equiv.natSumNatEquivNat.linearOrder
  let b := (Finsupp.basisSingleOne : Module.Basis (ℕ ⊕ ℕ) R V).ExteriorAlgebra
  intro x z hxz
  apply b.repr.injective
  ext s : 1
  have h := congrArg (fun a => b.repr a s) hxz
  exact mul_left_cancel₀ hc (by simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h)

theorem d_betaDeletion (N m q : ℕ) (t : Fin (q + 1) → ℕ)
    (htN : ∀ i, t i < N) (htm : ∀ i, t i < m) :
    d N m (betaDeletion N q t) = 0 := by
  apply smul_injective (-y 0) (neg_ne_zero.mpr (MvPolynomial.X_ne_zero _))
  change -y 0 • d N m (betaDeletion N q t) = -y 0 • (0 : A)
  rw [smul_zero, ← map_smul, ← d_orderedA N m q t htN htm, d_squared]

/-- The actual free connecting expression from ET-04, with negative old tails. -/
def omega (N m q : ℕ) (t : Fin (q + 1) → ℕ) : A :=
  v 0 • orderedA (q + 1) t + etaPrime N m * betaDeletion N q t

theorem omega_is_cycle (N m q : ℕ) (hN : 0 < N) (hm : 0 < m)
    (t : Fin (q + 1) → ℕ) (htN : ∀ i, t i < N) (htm : ∀ i, t i < m) :
    d N m (omega N m q t) = 0 := by
  rw [omega, map_add, map_smul, d_orderedA N m q t htN htm,
    d_etaPrime_mul N m hN hm, d_betaDeletion N m q t htN htm, mul_zero, sub_zero,
    smul_smul, ← add_smul]
  have hscalar : v 0 * -y 0 + y 0 * v 0 = 0 := by ring
  rw [hscalar, zero_smul]

end TorusLinkHomology.UniversalTransfer
