import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Descent from relatively prime denominator-clearing factors

For a fraction over a unique factorization domain, an element clears its reduced
denominator exactly when their product comes from the original ring. Two
relatively prime denominator-clearing factors therefore imply that the fraction
itself comes from the original ring.

This is the arithmetic input for the finite-adjugate version of UEI-009 in
`proof/02_universal_exterior_identity.md`. It uses relative primality, without
assuming that the two factors generate the unit ideal.
-/

namespace TorusLinkHomology.Generation

variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- A denominator-clearing factor is divisible by the reduced denominator. -/
theorem den_dvd_of_isInteger_mul {a : R} {x : F}
    (h : IsLocalization.IsInteger R (algebraMap R F a * x)) :
    (IsFractionRing.den R x : R) ∣ a := by
  obtain ⟨c, hc⟩ := h
  have hx : x * algebraMap R F (IsFractionRing.den R x : R) =
      algebraMap R F (IsFractionRing.num R x) :=
    IsFractionRing.num_mul_den_eq_num_iff_eq.mpr rfl
  apply (IsFractionRing.num_den_reduced R x).symm.dvd_of_dvd_mul_right
  refine ⟨c, ?_⟩
  apply IsFractionRing.injective R F
  simp only [map_mul]
  rw [hc, mul_comm (algebraMap R F (IsFractionRing.den R x : R)), mul_assoc, hx]

/-- A factor clears a fraction's denominator precisely when the reduced
denominator divides that factor. -/
theorem isInteger_mul_iff_den_dvd (a : R) (x : F) :
    IsLocalization.IsInteger R (algebraMap R F a * x) ↔
      (IsFractionRing.den R x : R) ∣ a := by
  constructor
  · exact den_dvd_of_isInteger_mul
  · rintro ⟨b, rfl⟩
    have hx : x * algebraMap R F (IsFractionRing.den R x : R) =
        algebraMap R F (IsFractionRing.num R x) :=
      IsFractionRing.num_mul_den_eq_num_iff_eq.mpr rfl
    refine ⟨b * IsFractionRing.num R x, ?_⟩
    simp only [map_mul]
    rw [← hx]
    ac_rfl

/-- A fraction cleared by two relatively prime elements already belongs to the
coefficient ring. No Bézout identity is required. -/
theorem isInteger_of_isRelPrime_mul {a b : R} {x : F}
    (hab : IsRelPrime a b)
    (ha : IsLocalization.IsInteger R (algebraMap R F a * x))
    (hb : IsLocalization.IsInteger R (algebraMap R F b * x)) :
    IsLocalization.IsInteger R x := by
  apply IsFractionRing.isInteger_of_isUnit_den
  exact hab (den_dvd_of_isInteger_mul ha) (den_dvd_of_isInteger_mul hb)

/-- Powers of two relatively prime elements also suffice to clear denominators.
The exponents may differ and may be zero. -/
theorem isInteger_of_isRelPrime_pow_mul {a b : R} {x : F}
    (hab : IsRelPrime a b) (m n : ℕ)
    (ha : IsLocalization.IsInteger R (algebraMap R F (a ^ m) * x))
    (hb : IsLocalization.IsInteger R (algebraMap R F (b ^ n) * x)) :
    IsLocalization.IsInteger R x :=
  isInteger_of_isRelPrime_mul hab.pow ha hb

end TorusLinkHomology.Generation
