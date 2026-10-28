import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! # The signed differential of ordered exterior products -/

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Contraction deletes each factor in turn, with its position sign.
`Fin.succAbove` retains the original order of every remaining factor. -/
theorem contractLeft_ιMulti (f : Module.Dual R M) (q : ℕ) (v : Fin (q + 1) → M) :
    CliffordAlgebra.contractLeft (Q := 0) f (ιMulti R (q + 1) v) =
      ∑ i : Fin (q + 1), ((-1 : R) ^ i.val * f (v i)) •
        ιMulti R q (v ∘ i.succAbove) := by
  induction q with
  | zero =>
    simp [ιMulti_succ_apply, ιMulti_zero_apply,
      CliffordAlgebra.contractLeft_ι, Algebra.algebraMap_eq_smul_one]
  | succ q ih =>
    conv_lhs => rw [ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [ιMulti_succ_apply]
    have htail : (v ∘ i.succ.succAbove) ∘ Fin.succ =
        (v ∘ Fin.succ) ∘ i.succAbove := by
      funext j
      simp only [Function.comp_apply, Fin.succ_succAbove_succ]
    rw [show Matrix.vecTail (v ∘ i.succ.succAbove) =
      (v ∘ i.succ.succAbove) ∘ Fin.succ from rfl, htail]
    simp only [Fin.val_succ, pow_succ, mul_neg, mul_one, neg_mul, neg_smul,
      Function.comp_apply, Matrix.vecTail, Fin.succ_succAbove_zero,
      mul_smul_comm]

/-- The alternating deletion expression is always a cycle. -/
theorem contractLeft_signed_deletion_eq_zero (f : Module.Dual R M) (q : ℕ)
    (v : Fin (q + 1) → M) :
    CliffordAlgebra.contractLeft (Q := 0) f
      (∑ i : Fin (q + 1), ((-1 : R) ^ i.val * f (v i)) •
        ιMulti R q (v ∘ i.succAbove)) = 0 := by
  rw [← contractLeft_ιMulti]
  exact CliffordAlgebra.contractLeft_contractLeft _ _

end ExteriorAlgebra
