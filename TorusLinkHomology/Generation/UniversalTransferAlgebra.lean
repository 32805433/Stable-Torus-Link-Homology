import DGA.Exterior
import TorusLinkHomology.Generation.CoefficientSeries
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The free polynomial exterior algebra for exceptional transfers

The two copies of `ℕ` index the even families `y,v` and the odd families
`A,Q`. Every chain is a finite polynomial/exterior expression; only the
coefficient series used to organize these expressions have infinite support.
The differential is an exterior contraction, so square zero does not rely
on the generation theorem or on formal series manipulations.
-/

noncomputable section

namespace TorusLinkHomology.UniversalTransfer

open scoped BigOperators

abbrev R := MvPolynomial (ℕ ⊕ ℕ) ℚ
abbrev V := (ℕ ⊕ ℕ) →₀ R
abbrev A := ExteriorAlgebra R V

def y (i : ℕ) : R := MvPolynomial.X (Sum.inl i)
def v (j : ℕ) : R := MvPolynomial.X (Sum.inr j)
def oddA (i : ℕ) : A := ExteriorAlgebra.ι R (Finsupp.single (Sum.inl i) 1)
def oddQ (h : ℕ) : A := ExteriorAlgebra.ι R (Finsupp.single (Sum.inr h) 1)

def ySeries : PowerSeries R := PowerSeries.mk y
def vSeries : PowerSeries R := PowerSeries.mk v

/-- The coefficient of the N-th power of the free even coefficient series. -/
def g (N i : ℕ) : R := (ySeries ^ N).coeff i

/-- Align V's upper exponent with that of C, whose bound is larger by m. -/
def shiftedV (m i : ℕ) : R := if m ≤ i then v (i - m) else 0

/-- Differential of a free Q-generator, with signed integer exponents. -/
def qEquation (N m h : ℕ) : R :=
  MvPolynomial.C ((N : ℚ)⁻¹) *
    ∑ ij ∈ Finset.antidiagonal h,
      (((-(m : ℤ) + (N : ℤ) * (ij.1 : ℤ) - (ij.2 : ℤ)) : ℤ) : R) *
        y ij.1 * v ij.2

def equation (N m : ℕ) : ℕ ⊕ ℕ → R
  | Sum.inl i => shiftedV m i - g N i
  | Sum.inr h => qEquation N m h

def functional (N m : ℕ) : Module.Dual R V :=
  Finsupp.linearCombination R (equation N m)

def dga (N m : ℕ) : DGA R A := ExteriorAlgebra.koszulDGA R V (functional N m)
abbrev d (N m : ℕ) : A →ₗ[R] A := (dga N m).d

theorem d_squared (N m : ℕ) (a : A) : d N m (d N m a) = 0 :=
  (dga N m).d_squared a

@[simp] theorem d_scalar (N m : ℕ) (r : R) : d N m (algebraMap R A r) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap _ _ _

@[simp] theorem d_oddA (N m i : ℕ) :
    d N m (oddA i) = algebraMap R A (shiftedV m i - g N i) := by
  simp [d, dga, oddA, functional, equation]

@[simp] theorem d_oddQ (N m h : ℕ) :
    d N m (oddQ h) = algebraMap R A (qEquation N m h) := by
  simp [d, dga, oddQ, functional, equation]

/-- The free exterior families packaged as series of exponent deficits. -/
def cSeries : PowerSeries A := PowerSeries.mk oddA
def qSeries : PowerSeries A := PowerSeries.mk oddQ

def dSeries (N m : ℕ) (f : PowerSeries A) : PowerSeries A :=
  CoefficientSeries.mapCoefficients (d N m).toAddMonoidHom f

@[simp] theorem coeff_dSeries (N m : ℕ) (f : PowerSeries A) (i : ℕ) :
    (dSeries N m f).coeff i = d N m (f.coeff i) :=
  CoefficientSeries.coeff_mapCoefficients _ _ _

theorem dSeries_squared (N m : ℕ) (f : PowerSeries A) :
    dSeries N m (dSeries N m f) = 0 := by
  ext i
  simp only [coeff_dSeries, d_squared, map_zero]

/-- The series differential commutes with Euler differentiation at any
signed upper exponent. -/
theorem dSeries_shiftedEuler (N m : ℕ) (b : ℤ) (f : PowerSeries A) :
    dSeries N m (CoefficientSeries.shiftedEuler b f) =
      CoefficientSeries.shiftedEuler b (dSeries N m f) :=
  CoefficientSeries.mapCoefficients_shiftedEuler _ _ _

/-- ET-08's identity dC=V−U^N, after aligning the upper exponent bounds. -/
theorem dSeries_cSeries (N m : ℕ) :
    dSeries N m cSeries =
      PowerSeries.map (algebraMap R A) (PowerSeries.mk (shiftedV m) - ySeries ^ N) := by
  ext i
  simp only [coeff_dSeries, cSeries, PowerSeries.coeff_mk, d_oddA,
    PowerSeries.coeff_map, map_sub, g]

/-- The coefficientwise defining identity for the universal Q series. -/
theorem dSeries_qSeries (N m : ℕ) :
    dSeries N m qSeries =
      PowerSeries.map (algebraMap R A) (PowerSeries.mk (qEquation N m)) := by
  ext h
  simp [qSeries]

/-- The leading Q equation has the negative sign required by eta-prime. -/
theorem qEquation_zero (N m : ℕ) :
    qEquation N m 0 = MvPolynomial.C ((N : ℚ)⁻¹) * (-(m : R) * y 0 * v 0) := by
  simp [qEquation]

/-- The signed coefficient formula is precisely N⁻¹S_N(V), with the
upper bounds r and ell, once Nr=ell+m. -/
theorem qEquation_eq_euler_coefficient (N m r ell h : ℕ) (hbound : N * r = ell + m) :
    qEquation N m h = MvPolynomial.C ((N : ℚ)⁻¹) *
      (ySeries * CoefficientSeries.shiftedEuler (ell : ℤ) vSeries -
        N • (CoefficientSeries.shiftedEuler (r : ℤ) ySeries * vSeries)).coeff h := by
  have hco (i j : ℕ) :
      (((-(m : ℤ) + (N : ℤ) * (i : ℤ) - (j : ℤ)) : ℤ) : R) =
        (ell : R) - (j : R) - (N : R) * ((r : R) - (i : R)) := by
    have hn : (N : R) * (r : R) = (ell : R) + (m : R) := by
      simpa only [Nat.cast_mul, Nat.cast_add] using congrArg (fun z : ℕ => (z : R)) hbound
    push_cast
    calc
      _ = ((N : R) * (r : R) - (m : R)) - (j : R) -
          (N : R) * ((r : R) - (i : R)) := by ring
      _ = _ := by rw [hn]; ring
  unfold qEquation
  congr 1
  simp only [map_sub, map_nsmul, PowerSeries.coeff_mul, Finset.smul_sum,
    ← Finset.sum_sub_distrib, CoefficientSeries.coeff_shiftedEuler,
    ySeries, vSeries, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro ij _
  rw [hco]
  simp only [← Int.cast_smul_eq_zsmul R, smul_eq_mul, nsmul_eq_mul,
    Int.cast_sub, Int.cast_natCast]
  ring

/-- ET-08's second series identity, stated inside the even coefficient ring
before embedding it in the exterior algebra. -/
theorem qEquation_series (N m r ell : ℕ) (hbound : N * r = ell + m) :
    PowerSeries.mk (qEquation N m) =
      PowerSeries.C (MvPolynomial.C ((N : ℚ)⁻¹)) *
        (ySeries * CoefficientSeries.shiftedEuler (ell : ℤ) vSeries -
          N • (CoefficientSeries.shiftedEuler (r : ℤ) ySeries * vSeries)) := by
  ext h : 1
  simpa only [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul] using
    qEquation_eq_euler_coefficient N m r ell h hbound

/-- The Q_h equation contains no v-variable of index above h. -/
theorem pderiv_qEquation_of_lt (N m h j : ℕ) (hj : h < j) :
    MvPolynomial.pderiv (Sum.inr j) (qEquation N m h) = 0 := by
  rw [qEquation, MvPolynomial.pderiv_C_mul, map_sum]
  have hs : ∑ ij ∈ Finset.antidiagonal h,
      MvPolynomial.pderiv (Sum.inr j)
        ((((-(m : ℤ) + (N : ℤ) * (ij.1 : ℤ) - (ij.2 : ℤ)) : ℤ) : R) *
          y ij.1 * v ij.2) = 0 := by
    apply Finset.sum_eq_zero
    intro ij hij
    have hsum := Finset.mem_antidiagonal.mp hij
    have hne : ij.2 ≠ j := by omega
    simp [y, v, MvPolynomial.pderiv_X, hne]
  rw [hs, mul_zero]

/-- The highest v-coefficient is −(m+h)y₀/N. This triangular coefficient
is the input for uniqueness before any localization or specialization. -/
theorem pderiv_qEquation_top (N m h : ℕ) :
    MvPolynomial.pderiv (Sum.inr h) (qEquation N m h) =
      MvPolynomial.C ((N : ℚ)⁻¹) * (-((m : R) + (h : R)) * y 0) := by
  rw [qEquation, MvPolynomial.pderiv_C_mul, map_sum]
  congr 1
  rw [Finset.sum_eq_single (0, h)]
  · simp [y, v, sub_eq_add_neg, add_comm]
  · intro ij hij hne
    have hsum := Finset.mem_antidiagonal.mp hij
    have hne' : ij.2 ≠ h := by
      intro heq
      apply hne
      ext <;> simp_all
    simp [y, v, MvPolynomial.pderiv_X, hne']
  · intro hnot
    exact False.elim (hnot (by simp))

theorem pderiv_qEquation_top_ne_zero (N m h : ℕ) (hN : 0 < N) (hm : 0 < m) :
    MvPolynomial.pderiv (Sum.inr h) (qEquation N m h) ≠ 0 := by
  rw [pderiv_qEquation_top]
  apply mul_ne_zero
  · exact MvPolynomial.C_ne_zero.mpr (inv_ne_zero (Nat.cast_ne_zero.mpr (by omega)))
  · apply mul_ne_zero
    · apply neg_ne_zero.mpr
      rw [← Nat.cast_add]
      change MvPolynomial.C ((m + h : ℕ) : ℚ) ≠ 0
      exact MvPolynomial.C_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
    · exact MvPolynomial.X_ne_zero _

end TorusLinkHomology.UniversalTransfer
