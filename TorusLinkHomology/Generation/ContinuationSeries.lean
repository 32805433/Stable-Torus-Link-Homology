import TorusLinkHomology.Generation.UniversalTransferCycles
import DGA.PowerSeriesAlgebra

/-!
# Solving the Euler equation in deficit coordinates

Let `U` have upper exponent `r` and let `C` have upper exponent `Nr`. In deficit
coordinates, the coefficients of `U DC - N (DU) C` are the finite sums `eulerDeficit`.
The term of `C` at deficit `h` appears with coefficient `-h U₀`. So when `U₀` is
invertible the equation can be solved recursively, and a solution is determined
by its zeroth coefficient.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientSeries

/-- The Euler expression at matching upper exponents, written coefficientwise. -/
theorem coeff_expression {B : Type*} [Ring B] (N : ℕ) (r b : ℤ) (hb : b = (N : ℤ) * r)
    (U F : PowerSeries B) (h : ℕ) :
    (expression N r b U F).coeff h =
      ∑ ij ∈ Finset.antidiagonal h,
        ((N : ℤ) * (ij.1 : ℤ) - (ij.2 : ℤ)) • (U.coeff ij.1 * F.coeff ij.2) := by
  simp only [expression, map_sub, map_nsmul, PowerSeries.coeff_mul, coeff_shiftedEuler,
    Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  rw [mul_smul_comm, smul_mul_assoc, ← natCast_zsmul, smul_smul, ← sub_smul]
  congr 1
  rw [hb]
  ring

section Module

variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

/-- The coefficients of `U DC - N (DU) C` for a module-valued sequence `C`. -/
def eulerDeficit (N : ℕ) (U : PowerSeries S) (C : ℕ → M) (h : ℕ) : M :=
  ∑ ij ∈ Finset.antidiagonal h,
    ((N : ℤ) * (ij.1 : ℤ) - (ij.2 : ℤ)) • (U.coeff ij.1 • C ij.2)

/-- The term of `C` at the top deficit, separated from the earlier ones. -/
theorem eulerDeficit_eq (N : ℕ) (U : PowerSeries S) (C : ℕ → M) (h : ℕ) :
    eulerDeficit N U C h = (-(h : ℤ)) • (U.coeff 0 • C h) +
      ∑ j : Fin h, ((N : ℤ) * ((h - j.val : ℕ) : ℤ) - (j.val : ℤ)) •
        (U.coeff (h - j.val) • C j.val) := by
  rw [eulerDeficit, ← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => ((N : ℤ) * (b : ℤ) - (a : ℤ)) • (U.coeff b • C a)),
    Finset.sum_range_succ, Finset.sum_range, add_comm]
  simp

@[simp] theorem eulerDeficit_zero (N : ℕ) (U : PowerSeries S) (C : ℕ → M) :
    eulerDeficit N U C 0 = 0 := by
  simp [eulerDeficit_eq]

/-- Coefficient maps commute with the Euler coefficients. -/
theorem map_eulerDeficit {T M' : Type*} [CommRing T] [AddCommGroup M'] [Module T M']
    (φ : S →+* T) (g : M →ₛₗ[φ] M') (N : ℕ) (U : PowerSeries S) (C : ℕ → M) (h : ℕ) :
    g (eulerDeficit N U C h) = eulerDeficit N (PowerSeries.map φ U) (fun k => g (C k)) h := by
  simp only [eulerDeficit, map_sum, map_zsmul, g.map_smulₛₗ, PowerSeries.coeff_map]

/-- The Euler expression applied to a series of degree-one generators. -/
theorem coeff_expression_iotaSeries (N : ℕ) (r b : ℤ) (hb : b = (N : ℤ) * r)
    (U : PowerSeries S) (C : ℕ → M) (h : ℕ) :
    (expression N r b (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) U)
        (ExteriorAlgebra.iotaSeries (R := S) C)).coeff h =
      ExteriorAlgebra.ι S (eulerDeficit N U C h) := by
  rw [coeff_expression N r b hb, eulerDeficit, map_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [map_zsmul, map_smul, PowerSeries.coeff_map, ExteriorAlgebra.coeff_iotaSeries,
    ← Algebra.smul_def]

/-- The Euler expression applied to a scalar series. -/
theorem coeff_expression_scalar (N : ℕ) (r b : ℤ) (hb : b = (N : ℤ) * r)
    (U F : PowerSeries S) (h : ℕ) :
    (expression N r b U F).coeff h = eulerDeficit N U (fun k => F.coeff k) h := by
  rw [coeff_expression N r b hb, eulerDeficit]
  simp only [smul_eq_mul]

end Module

section Field

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- The solution of the Euler equation with prescribed forcing and leading term. -/
def eulerSolution (N : ℕ) (U : PowerSeries F) (P : ℕ → M) (C₀ : M) (h : ℕ) : M :=
  if _hh : h = 0 then C₀
  else ((h : F) * U.coeff 0)⁻¹ •
    ((∑ j : Fin h, ((N : ℤ) * ((h - j.val : ℕ) : ℤ) - (j.val : ℤ)) •
        (U.coeff (h - j.val) • eulerSolution N U P C₀ j.val)) - P h)
termination_by h
decreasing_by exact j.isLt

@[simp] theorem eulerSolution_zero (N : ℕ) (U : PowerSeries F) (P : ℕ → M) (C₀ : M) :
    eulerSolution N U P C₀ 0 = C₀ := by
  rw [eulerSolution, dif_pos rfl]

/-- Away from deficit zero, the solution satisfies the prescribed equation. -/
theorem eulerDeficit_eulerSolution [CharZero F] (N : ℕ) (U : PowerSeries F) (hU : U.coeff 0 ≠ 0)
    (P : ℕ → M) (C₀ : M) (h : ℕ) (hh : h ≠ 0) :
    eulerDeficit N U (eulerSolution N U P C₀) h = P h := by
  rw [eulerDeficit_eq]
  conv_lhs => rw [eulerSolution, dif_neg hh]
  have hF : (h : F) ≠ 0 := Nat.cast_ne_zero.mpr hh
  rw [← Int.cast_smul_eq_zsmul F, smul_smul, smul_smul]
  have hscalar : ((-(h : ℤ) : ℤ) : F) * U.coeff 0 * ((h : F) * U.coeff 0)⁻¹ = -1 := by
    push_cast
    field_simp
  rw [hscalar, neg_smul, one_smul]
  abel

/-- Two sequences satisfying the same equation up to `K` with the same leading
term agree up to `K`. -/
theorem eq_of_eulerDeficit_eq [CharZero F] (N : ℕ) (U : PowerSeries F) (hU : U.coeff 0 ≠ 0)
    (A B : ℕ → M) (K : ℕ) (h₀ : A 0 = B 0)
    (hA : ∀ h, h ≠ 0 → h ≤ K → eulerDeficit N U A h = eulerDeficit N U B h)
    (h : ℕ) (hK : h ≤ K) : A h = B h := by
  induction h using Nat.strong_induction_on with
  | h h ih =>
    by_cases hh : h = 0
    · rw [hh, h₀]
    have heq := hA h hh hK
    rw [eulerDeficit_eq, eulerDeficit_eq] at heq
    have hsum : (∑ j : Fin h, ((N : ℤ) * ((h - j.val : ℕ) : ℤ) - (j.val : ℤ)) •
          (U.coeff (h - j.val) • A j.val)) =
        ∑ j : Fin h, ((N : ℤ) * ((h - j.val : ℕ) : ℤ) - (j.val : ℤ)) •
          (U.coeff (h - j.val) • B j.val) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j.val j.isLt (j.isLt.le.trans hK)]
    rw [hsum, add_left_inj, ← Int.cast_smul_eq_zsmul F, ← Int.cast_smul_eq_zsmul F,
      smul_smul, smul_smul] at heq
    have hne : ((-(h : ℤ) : ℤ) : F) * U.coeff 0 ≠ 0 := by
      apply mul_ne_zero _ hU
      simpa using hh
    exact smul_right_injective M hne heq

end Field

end TorusLinkHomology.CoefficientSeries
