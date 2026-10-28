import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Ordered products of power series

Coefficient formulas use lists so that the coefficient algebra need not be
commutative. Only addition of coefficients is commutative.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientSeries

variable {A : Type*} [Semiring A]

/-- The convolution formula for an ordered product over a finite tuple. -/
theorem coeff_orderedProduct {q : ℕ} (f : Fin q → PowerSeries A) (D : ℕ) :
    ((List.ofFn f).prod).coeff D =
      ((List.Nat.antidiagonalTuple q D).map
        (fun i => (List.ofFn (fun a => (f a).coeff (i a))).prod)).sum := by
  induction q generalizing D with
  | zero =>
    cases D <;> simp
  | succ q ih =>
    rw [List.ofFn_succ, List.prod_cons, PowerSeries.coeff_mul]
    simp only [List.Nat.antidiagonalTuple, List.flatMap_def, List.map_flatten, List.sum_flatten,
      List.map_map, Function.comp_def]
    have h (ij : ℕ × ℕ) :
        (f 0).coeff ij.1 * ((List.ofFn (fun a => f a.succ)).prod).coeff ij.2 =
        ((List.Nat.antidiagonalTuple q ij.2).map
          (fun i => (List.ofFn (fun a => (f a).coeff (Fin.cons ij.1 i a))).prod)).sum := by
      rw [ih]
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]
      rw [← List.sum_map_mul_left]
    simp_rw [← h]
    rfl

/-- Finite-range form of the ordered coefficient formula. Every contributing
index is at most `D`, so a cutoff strictly above `D` loses no term. -/
theorem coeff_orderedProduct_eq_sum_fin {q : ℕ} (f : Fin q → PowerSeries A)
    (D L : ℕ) (hDL : D < L) :
    ((List.ofFn f).prod).coeff D =
      ∑ i : Fin q → Fin L, if ∑ a : Fin q, (i a).val = D then
        (List.ofFn (fun a => (f a).coeff (i a).val)).prod else 0 := by
  classical
  rw [coeff_orderedProduct]
  change (∑ i ∈ Finset.Nat.antidiagonalTuple q D,
    (List.ofFn (fun a => (f a).coeff (i a))).prod) = _
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun i _ => fun a => (i a).val)
  · intro i hi
    exact Finset.Nat.mem_antidiagonalTuple.mpr (Finset.mem_filter.mp hi).2
  · intro i _ j _ hij
    funext a
    exact Fin.ext (congrFun hij a)
  · intro i hi
    have hsum := Finset.Nat.mem_antidiagonalTuple.mp hi
    have hbound (a : Fin q) : i a < L := by
      have hle : i a ≤ ∑ b, i b := Finset.single_le_sum (fun b _ => Nat.zero_le (i b))
        (Finset.mem_univ a)
      omega
    let j : Fin q → Fin L := fun a => ⟨i a, hbound a⟩
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact hsum
  · intro i _
    rfl

/-- A separate leading factor has its own deficit; every other factor stays
in its original order. -/
theorem coeff_mul_orderedProduct_eq_sum_fin {q : ℕ} (v : PowerSeries A)
    (f : Fin q → PowerSeries A) (D L : ℕ) (hDL : D < L) :
    (v * (List.ofFn f).prod).coeff D =
      ∑ j : Fin L, ∑ i : Fin q → Fin L,
        if j.val + ∑ a : Fin q, (i a).val = D then
          v.coeff j.val * (List.ofFn (fun a => (f a).coeff (i a).val)).prod else 0 := by
  have h := coeff_orderedProduct_eq_sum_fin (Fin.cons v f) D L hDL
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons] at h
  rw [h, ← (Fin.consEquiv (fun _ : Fin (q + 1) => Fin L)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

end TorusLinkHomology.CoefficientSeries
