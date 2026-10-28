import TorusLinkHomology.MuCycles

/-!
# Elementary boundary cases for coefficient Koszul homology

With no generators, every chain is a coefficient. With one exterior generator,
the nonzero differential makes every cycle a coefficient as well.
The public proof keeps the zero-variable case. The proved one-variable lemma
is retained for reuse; positive lengths follow the uniform auxiliary argument.
-/

noncomputable section

namespace TorusLinkHomology.Generation

/-- With no variables, all chains belong to the coefficient subalgebra. -/
theorem zero_variables (N : ℕ) :
    (∀ k : ℕ, 1 ≤ k → k < 0 → d N 0 (mu N 0 k) = 0) ∧
    (∀ a : A 0, d N 0 a = 0 →
      ∃ p : A 0, p ∈ muSubalgebra N 0 ∧ ∃ b : A 0, a = p + d N 0 b) := by
  constructor
  · intro k _ hk
    exact mu_is_cycle N 0 k hk
  · intro a hda
    clear hda
    have ha : a ∈ muSubalgebra N 0 := by
      induction a using ExteriorAlgebra.induction with
      | algebraMap r => exact (muSubalgebra N 0).algebraMap_mem r
      | ι x =>
        have hx : x = 0 := by
          ext i
          exact Fin.elim0 i
        simp [hx]
      | mul a b ha hb => exact (muSubalgebra N 0).mul_mem ha hb
      | add a b ha hb => exact (muSubalgebra N 0).add_mem ha hb
    exact ⟨a, ha, 0, by simp⟩

private theorem one_variable_decomposition (a : A 1) :
    ∃ r s : R 1, a = r • (1 : A 1) + s • xi 1 0 := by
  have hsquare : xi 1 0 * xi 1 0 = 0 :=
    ExteriorAlgebra.ι_sq_zero _
  induction a using ExteriorAlgebra.induction with
  | algebraMap r => exact ⟨r, 0, by simp [Algebra.smul_def]⟩
  | ι x =>
    have hx : x = x 0 • Finsupp.single (0 : Fin 1) (1 : R 1) := by
      apply Finsupp.ext
      intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp
    refine ⟨0, x 0, ?_⟩
    rw [hx, map_smul]
    simp [xi]
  | mul a b ha hb =>
    obtain ⟨r, s, rfl⟩ := ha
    obtain ⟨r', s', rfl⟩ := hb
    refine ⟨r * r', r * s' + s * r', ?_⟩
    simp [add_mul, mul_add, smul_smul, hsquare, add_smul, mul_comm]
    abel
  | add a b ha hb =>
    obtain ⟨r, s, rfl⟩ := ha
    obtain ⟨r', s', rfl⟩ := hb
    refine ⟨r + r', s + s', ?_⟩
    simp only [add_smul]
    abel

private theorem coefficient_one_variable (N : ℕ) :
    differentialCoefficient N 1 0 = u 1 0 ^ N := by
  have hu : uPolynomial 1 = Polynomial.C (u 1 0) := by simp [uPolynomial]
  rw [differentialCoefficient, hu, ← Polynomial.C_pow]
  exact Polynomial.coeff_C_zero

/-- At length one the sole equation is a nonzero power of a polynomial variable,
so every cycle is a coefficient. This also includes exponent zero. -/
theorem one_variable (N : ℕ) :
    (∀ k : ℕ, 1 ≤ k → k < 1 → d N 1 (mu N 1 k) = 0) ∧
    (∀ a : A 1, d N 1 a = 0 →
      ∃ p : A 1, p ∈ muSubalgebra N 1 ∧ ∃ b : A 1, a = p + d N 1 b) := by
  constructor
  · intro k _ hk
    exact mu_is_cycle N 1 k hk
  · intro a ha
    obtain ⟨r, s, rfl⟩ := one_variable_decomposition a
    have hs : s = 0 := by
      have hd : algebraMap (R 1) (A 1) (s * u 1 0 ^ N) = 0 := by
        rw [map_add, map_smul, map_smul] at ha
        have hdone : d N 1 (1 : A 1) = 0 := by simpa using d_scalar N 1 1
        rw [hdone, smul_zero, zero_add, d_xi, coefficient_one_variable] at ha
        simpa only [Algebra.smul_def, ← map_mul] using ha
      have hprod : s * u 1 0 ^ N = 0 :=
        (ExteriorAlgebra.algebraMap_eq_zero_iff (V 1) _).mp hd
      exact (mul_eq_zero.mp hprod).resolve_right
        (pow_ne_zero N (MvPolynomial.X_ne_zero (0 : Fin 1)))
    refine ⟨r • (1 : A 1), ?_, 0, ?_⟩
    · exact (muSubalgebra N 1).smul_mem (muSubalgebra N 1).one_mem r
    · simp [hs]

end TorusLinkHomology.Generation
