import TorusLinkHomology.Generation.UniversalTransferAlgebra
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Exact polynomial quotients at the leading coefficient

The quotient is constructed by a finite geometric sum before specialization.
No coefficient variable, chain, or homology class is divided by.
-/

noncomputable section

namespace TorusLinkHomology.CoefficientSeries

open scoped BigOperators

variable {S T : Type*} [CommRing S] [CommRing T]

/-- Remove the leading coefficient in the series-of-deficits convention. -/
def removeConstant (F : PowerSeries S) : PowerSeries S := F - PowerSeries.C (F.coeff 0)

/-- A finite geometric sum witnessing division of the difference of powers. -/
def leadingQuotientSeries (N : ℕ) (F : PowerSeries S) : PowerSeries S :=
  ∑ a ∈ Finset.range N, F ^ a * removeConstant F ^ (N - 1 - a)

def leadingQuotient (N : ℕ) (F : PowerSeries S) (t : ℕ) : S :=
  (leadingQuotientSeries N F).coeff t

theorem constant_mul_leadingQuotientSeries (N : ℕ) (F : PowerSeries S) :
    PowerSeries.C (F.coeff 0) * leadingQuotientSeries N F =
      F ^ N - removeConstant F ^ N := by
  have h := (Commute.all F (removeConstant F)).mul_geom_sum₂ N
  simpa only [leadingQuotientSeries, removeConstant, sub_sub_cancel] using h

theorem coeff_removeConstant_pow_eq_zero (N t : ℕ) (F : PowerSeries S) (ht : t < N) :
    (removeConstant F ^ N).coeff t = 0 := by
  have hdiv : PowerSeries.X ∣ removeConstant F := by
    apply PowerSeries.X_dvd_iff.mpr
    simp [removeConstant, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hdiv N) t ht

/-- Every coefficient below deficit N is divisible by the constant term,
with the displayed finite polynomial quotient. -/
theorem coeff_pow_eq_constant_mul_leadingQuotient (N t : ℕ) (F : PowerSeries S)
    (ht : t < N) : (F ^ N).coeff t = F.coeff 0 * leadingQuotient N F t := by
  have h := congrArg (PowerSeries.coeff t) (constant_mul_leadingQuotientSeries N F)
  rw [PowerSeries.coeff_C_mul, map_sub, coeff_removeConstant_pow_eq_zero N t F ht,
    sub_zero] at h
  exact h.symm

theorem map_removeConstant (f : S →+* T) (F : PowerSeries S) :
    PowerSeries.map f (removeConstant F) = removeConstant (PowerSeries.map f F) := by
  simp [removeConstant]

/-- Construction of the quotient commutes with every coefficient homomorphism,
including ones which send the leading coefficient to zero. -/
theorem map_leadingQuotient (f : S →+* T) (N t : ℕ) (F : PowerSeries S) :
    f (leadingQuotient N F t) = leadingQuotient N (PowerSeries.map f F) t := by
  unfold leadingQuotient
  rw [← PowerSeries.coeff_map]
  congr 1
  simp only [leadingQuotientSeries, map_sum, map_mul, map_pow, map_removeConstant]

end TorusLinkHomology.CoefficientSeries

namespace TorusLinkHomology.UniversalTransfer

/-- The free polynomial beta_t, constructed without division by y₀. -/
def beta (N t : ℕ) : R := CoefficientSeries.leadingQuotient N ySeries t

theorem g_eq_y_mul_beta (N t : ℕ) (ht : t < N) : g N t = y 0 * beta N t := by
  simpa only [g, beta, ySeries, PowerSeries.coeff_mk] using
    CoefficientSeries.coeff_pow_eq_constant_mul_leadingQuotient N t ySeries ht

/-- The exact quotient is unique in the free polynomial ring. -/
theorem beta_unique (N t : ℕ) (ht : t < N) (b : R) (hb : g N t = y 0 * b) :
    beta N t = b := by
  apply mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := ℚ) (Sum.inl 0))
  exact (g_eq_y_mul_beta N t ht).symm.trans hb

end TorusLinkHomology.UniversalTransfer
