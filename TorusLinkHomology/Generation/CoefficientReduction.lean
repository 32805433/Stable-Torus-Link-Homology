import TorusLinkHomology.Generation.Comparison

/-!
# Exactness of reduction in the last coefficient variable

The inclusion of the first `r` coefficient variables is a section of the map
setting the last variable to zero. Every polynomial differs from its reduced
and re-included value by a multiple of that last variable.
-/

noncomputable section

namespace TorusLinkHomology.CoefficientComplex

/-- Include the first coefficient variables, leaving the last variable unused. -/
def includeCoefficients (r : ℕ) : R r →ₐ[ℚ] R (r + 1) :=
  MvPolynomial.rename Fin.castSucc

@[simp] theorem includeCoefficients_e (r : ℕ) (i : Fin r) :
    includeCoefficients r (e r i) = e (r + 1) i.castSucc := by
  simp [includeCoefficients, e]

/-- Reducing after inclusion is the identity on the smaller coefficient ring. -/
@[simp] theorem reduceCoefficients_include (r : ℕ) (c : R r) :
    reduceCoefficients r (includeCoefficients r c) = c := by
  have h : (reduceCoefficients r).comp (includeCoefficients r) = AlgHom.id ℚ (R r) := by
    apply MvPolynomial.algHom_ext
    intro i
    change reduceCoefficients r (includeCoefficients r (e r i)) = e r i
    rw [includeCoefficients_e, reduceCoefficients_e_castSucc]
  exact AlgHom.congr_fun h c

/-- Inclusion of the smaller coefficient ring is injective. -/
theorem includeCoefficients_injective (r : ℕ) : Function.Injective (includeCoefficients r) :=
  Function.LeftInverse.injective (reduceCoefficients_include r)

/-- Every coefficient in the smaller ring has its evident polynomial lift. -/
theorem reduceCoefficients_surjective (r : ℕ) : Function.Surjective (reduceCoefficients r) :=
  fun c => ⟨includeCoefficients r c, reduceCoefficients_include r c⟩

/-- The remainder after reduction and re-inclusion is divisible by the last
coefficient variable. The witness is polynomial, before any specialization. -/
theorem coefficient_remainder_divisible (r : ℕ) (c : R (r + 1)) :
    ∃ b : R (r + 1), c - includeCoefficients r (reduceCoefficients r c) =
      e (r + 1) (Fin.last r) * b := by
  induction c using MvPolynomial.induction_on with
  | C q =>
    refine ⟨0, ?_⟩
    simp [includeCoefficients, reduceCoefficients]
  | add p q hp hq =>
    obtain ⟨b, hb⟩ := hp
    obtain ⟨d, hd⟩ := hq
    refine ⟨b + d, ?_⟩
    simp only [map_add, mul_add]
    rw [← hb, ← hd]
    abel
  | mul_X p i hp =>
    obtain ⟨b, hb⟩ := hp
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine ⟨p, ?_⟩
      change p * e (r + 1) (Fin.last r) -
        includeCoefficients r (reduceCoefficients r (p * e (r + 1) (Fin.last r))) = _
      simp [mul_comm]
    · refine ⟨b * e (r + 1) i.castSucc, ?_⟩
      change p * e (r + 1) i.castSucc -
        includeCoefficients r (reduceCoefficients r (p * e (r + 1) i.castSucc)) = _
      rw [map_mul, reduceCoefficients_e_castSucc, map_mul, includeCoefficients_e,
        ← sub_mul, hb, mul_assoc]

/-- The coefficient reduction has kernel exactly the principal ideal generated
by the last coefficient variable. -/
theorem reduceCoefficients_eq_zero_iff (r : ℕ) (c : R (r + 1)) :
    reduceCoefficients r c = 0 ↔
      ∃ b : R (r + 1), c = e (r + 1) (Fin.last r) * b := by
  constructor
  · intro hc
    simpa [hc] using coefficient_remainder_divisible r c
  · rintro ⟨b, rfl⟩
    simp

end TorusLinkHomology.CoefficientComplex
