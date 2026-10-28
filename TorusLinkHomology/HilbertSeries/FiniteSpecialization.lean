import TorusLinkHomology.HilbertSeries.InitialSeries
import TorusLinkHomology.HilbertSeries.FiniteRecurrence
import TorusLinkHomology.HilbertSeries.QSeries.SpecializationApplications

/-! Positive specializations of the explicit finite numerator recurrence. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- Polynomial substitution s ↦ sv, with v and z fixed. -/
def shiftPolynomial : MvPolynomial (Fin 3) ℚ →+* Series :=
  MvPolynomial.eval₂Hom MvPowerSeries.C
    ![MvPowerSeries.X 0 * MvPowerSeries.X 1, MvPowerSeries.X 1, MvPowerSeries.X 2]

private theorem polynomial_monomial_tridegree (a b h : ℕ) (q : ℚ) :
    MvPolynomial.monomial (tridegree a b h) q =
      MvPolynomial.C q * (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) ^ a *
        MvPolynomial.X 1 ^ b * MvPolynomial.X 2 ^ h := by
  simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_apply,
    MvPolynomial.monomial_mul, zero_add, mul_one, tridegree]

theorem shiftPolynomial_monomial (a b h : ℕ) (q : ℚ) :
    shiftPolynomial (MvPolynomial.monomial (tridegree a b h) q) =
      MvPowerSeries.monomial (tridegree a (a + b) h) q := by
  rw [polynomial_monomial_tridegree]
  simp only [map_mul, map_pow, shiftPolynomial, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    mul_pow]
  simp only [MvPowerSeries.X_pow_eq, ← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.monomial_mul_monomial, zero_add, mul_one]
  apply congrArg (fun e : Fin 3 →₀ ℕ => MvPowerSeries.monomial e q)
  ext i
  fin_cases i <;> simp [tridegree, Finsupp.single_add]

private theorem polynomial_coe_sum (p : MvPolynomial (Fin 3) ℚ) :
    (p : Series) = ∑ e ∈ p.support, MvPowerSeries.monomial e (p.coeff e) := by
  simpa only [map_sum, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_monomial] using congrArg
      (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 3) (R := ℚ)) p.as_sum

/-- Shifting s to sv increases a support-cone bound by one. -/
theorem coneSupported_shiftPolynomial (C : ℕ) (p : MvPolynomial (Fin 3) ℚ)
    (hp : ConeSupported C (p : Series)) :
    ConeSupported (C + 1) (shiftPolynomial p) := by
  classical
  conv_rhs => rw [p.as_sum]
  rw [map_sum]
  intro d hd
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro e he
  have hb : e 1 ≤ C * e 0 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp he) (hp e (by omega))
  rw [← tridegree_eta e, shiftPolynomial_monomial]
  simpa only [tridegree_eta] using ConeSupported.monomial (C + 1) (e 0) (e 0 + e 1) (e 2) (p.coeff e)
    (by nlinarith) d hd

/-- The positive specialization of s ↦ sv is the specialization at r-1. -/
theorem positiveSpecialization_shiftPolynomial (C r : ℕ)
    (p : MvPolynomial (Fin 3) ℚ) (hr : C + 1 < r)
    (hp : ConeSupported C (p : Series)) :
    positiveSpecialization (C + 1) r (shiftPolynomial p) =
      positiveSpecialization C (r - 1) (p : Series) := by
  classical
  have hshift : shiftPolynomial p =
      ∑ e ∈ p.support, shiftPolynomial (MvPolynomial.monomial e (p.coeff e)) := by
    simpa only [map_sum] using congrArg shiftPolynomial p.as_sum
  rw [hshift, polynomial_coe_sum, positiveSpecialization_sum, positiveSpecialization_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hb : e 1 ≤ C * e 0 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp he) (hp e (by omega))
  rw [← tridegree_eta e, shiftPolynomial_monomial,
    positiveSpecialization_monomial (C + 1) r _ _ _ _ hr (by nlinarith),
    positiveSpecialization_monomial C (r - 1) _ _ _ _ (by omega) hb]
  have hs : r * e 0 - (e 0 + e 1) = (r - 1) * e 0 - e 1 := by
    rw [Nat.sub_mul]
    simp only [one_mul, Nat.sub_sub]
  rw [hs]


/-- The explicit numerator is a genuine polynomial in the three variables. -/
def finiteNumeratorPolynomial (N n : ℕ) : MvPolynomial (Fin 3) ℚ :=
  finiteNumeratorAt N n (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

theorem coe_finiteNumeratorPolynomial (N n : ℕ) :
    (finiteNumeratorPolynomial N n : Series) = finiteNumerator N n := by
  simpa only [finiteNumeratorPolynomial, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
    MvPolynomial.coe_X, finiteNumerator_eq_at] using
    map_finiteNumeratorAt (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 3) (R := ℚ))
      N n (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

theorem shift_finiteNumeratorPolynomial (N n : ℕ) :
    shiftPolynomial (finiteNumeratorPolynomial N n) =
      finiteNumeratorAt N n ((MvPowerSeries.X 0 : Series) * MvPowerSeries.X 1)
        (MvPowerSeries.X 1) (MvPowerSeries.X 2) := by
  rw [finiteNumeratorPolynomial, map_finiteNumeratorAt]
  simp [shiftPolynomial]

theorem coneSupported_finiteNumerator_shift (N n C : ℕ)
    (hf : ConeSupported C (finiteNumerator N n)) :
    ConeSupported (C + 1)
      (finiteNumeratorAt N n ((MvPowerSeries.X 0 : Series) * MvPowerSeries.X 1)
        (MvPowerSeries.X 1) (MvPowerSeries.X 2)) := by
  rw [← shift_finiteNumeratorPolynomial]
  apply coneSupported_shiftPolynomial
  simpa only [coe_finiteNumeratorPolynomial] using hf

theorem positiveSpecialization_finiteNumerator_shift (N n C r : ℕ)
    (hr : C + 1 < r) (hf : ConeSupported C (finiteNumerator N n)) :
    positiveSpecialization (C + 1) r
      (finiteNumeratorAt N n ((MvPowerSeries.X 0 : Series) * MvPowerSeries.X 1)
        (MvPowerSeries.X 1) (MvPowerSeries.X 2)) =
      positiveSpecialization C (r - 1) (finiteNumerator N n) := by
  rw [← shift_finiteNumeratorPolynomial]
  simpa only [coe_finiteNumeratorPolynomial] using
    positiveSpecialization_shiftPolynomial C r (finiteNumeratorPolynomial N n) hr
      (by simpa only [coe_finiteNumeratorPolynomial] using hf)

theorem negative_odd_monomial (N : ℕ) :
    (-(MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ N) =
      MvPowerSeries.monomial (tridegree N 0 1) (-1) := by
  rw [map_neg, monomial_tridegree_one]
  simp only [pow_zero, mul_one, pow_one]
  ring

theorem coneSupported_numeratorFactor (N n C : ℕ) (hn : n ≤ C * (N + 1)) :
    ConeSupported C
      (1 + (MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ (N + 1) * MvPowerSeries.X 1 ^ n) := by
  apply (coneSupported_one C).add
  convert coneSupported_svz C (N + 1) n 1 hn using 1
  ring

theorem coneSupported_numeratorCorrection (N n C : ℕ) (hN : 0 < N)
    (hn : n ≤ C * N) (hNC : N - 1 ≤ C * N) :
    ConeSupported C
      (((1 - MvPowerSeries.X 0) * (MvPowerSeries.X 0 : Series) ^ N * MvPowerSeries.X 1 ^ n) *
        qPochhammer (-MvPowerSeries.X 2 * MvPowerSeries.X 0 ^ N) (MvPowerSeries.X 1) N) := by
  have hs : ConeSupported C (MvPowerSeries.X 0 : Series) := by
    simpa using coneSupported_svz C 1 0 0 (by omega)
  have hsN : ConeSupported C ((MvPowerSeries.X 0 : Series) ^ N * MvPowerSeries.X 1 ^ n) := by
    simpa using coneSupported_svz C N n 0 hn
  have hq : ConeSupported C
      (qPochhammer (-MvPowerSeries.X 2 * (MvPowerSeries.X 0 : Series) ^ N) (MvPowerSeries.X 1) N) := by
    rw [negative_odd_monomial]
    apply coneSupported_qPochhammer_monomial
    intro j hj
    omega
  simpa only [mul_assoc] using ((coneSupported_one C).sub hs).mul (hsN.mul hq)

/-- The explicit numerator has the same weight-support cone as normalized homology. -/
theorem coneSupported_finiteNumerator (N n : ℕ) (hN : 0 < N) :
    ConeSupported (n - 1) (finiteNumerator N n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      rw [finiteNumerator_eq_initial_of_le N 0 (by omega), initialNumerator_zero]
      exact coneSupported_one _
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    by_cases hm : m ≤ N
    · rw [← finite_hilbert_series_shortRange N m hN hm]
      exact coneSupported_hilbertNumerator N (m + 1) m hN (by omega)
    · have hNm : N ≤ m := by omega
      rw [finiteNumerator_recurrence N m hNm]
      apply ConeSupported.sub
      · exact (coneSupported_numeratorFactor N m m (by nlinarith)).mul
          ((ih m (by omega)).mono (by omega))
      · apply (coneSupported_numeratorCorrection N m m hN (by nlinarith) (by have := Nat.sub_le N 1; nlinarith)).mul
        exact (coneSupported_finiteNumerator_shift N (m - N) (m - N - 1)
          (ih (m - N) (by omega))).mono (by omega)


private theorem charge_negative_monomial (w : ℕ) :
    (MvPowerSeries.monomial (Finsupp.single 0 w + Finsupp.single 1 1) (-1) : ChargeSeries) =
      -(MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ w) := by
  rw [map_neg]
  congr 1
  rw [MvPowerSeries.X_pow_eq]
  change _ = MvPowerSeries.monomial (Finsupp.single 1 1) 1 * _
  rw [MvPowerSeries.monomial_mul_monomial, one_mul, add_comm]

theorem positiveSpecialization_numeratorFactor (N n C r : ℕ)
    (hr : C < r) (hn : n ≤ C * (N + 1)) :
    positiveSpecialization C r
      (1 + (MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ (N + 1) * MvPowerSeries.X 1 ^ n) =
      1 + (MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ (r * (N + 1) - n) := by
  rw [positiveSpecialization_add, positiveSpecialization_one]
  congr 1
  have he : (MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ (N + 1) * MvPowerSeries.X 1 ^ n =
      MvPowerSeries.X 0 ^ (N + 1) * MvPowerSeries.X 1 ^ n * MvPowerSeries.X 2 ^ 1 := by ring
  rw [he, positiveSpecialization_svz C r (N + 1) n 1 hr hn, pow_one, mul_comm]

theorem positiveSpecialization_exteriorNumerator (N C r : ℕ)
    (hr : C < r) (hNC : N - 1 ≤ C * N) :
    positiveSpecialization C r
      (qPochhammer (-(MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ N)
        (MvPowerSeries.X 1) N) =
      ∏ j ∈ Finset.range N,
        (1 + (MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ (r * N - j)) := by
  rw [negative_odd_monomial,
    positiveSpecialization_qPochhammer_monomial C r N 0 1 N (-1) hr (by
      intro j hj; omega)]
  simp only [zero_add, charge_negative_monomial, sub_neg_eq_add]

theorem positiveSpecialization_numeratorCorrection (N n C r : ℕ) (hN : 0 < N)
    (hr : C < r) (hn : n ≤ C * N) (hNC : N - 1 ≤ C * N) :
    positiveSpecialization C r
      (((1 - MvPowerSeries.X 0) * (MvPowerSeries.X 0 : Series) ^ N * MvPowerSeries.X 1 ^ n) *
        qPochhammer (-MvPowerSeries.X 2 * MvPowerSeries.X 0 ^ N) (MvPowerSeries.X 1) N) =
      ((1 - (MvPowerSeries.X 0 : ChargeSeries) ^ r) * MvPowerSeries.X 0 ^ (r * N - n)) *
        ∏ j ∈ Finset.range N,
          (1 + (MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ (r * N - j)) := by
  have hs : ConeSupported C (MvPowerSeries.X 0 : Series) := by
    simpa using coneSupported_svz C 1 0 0 (by omega)
  have hsn : ConeSupported C ((MvPowerSeries.X 0 : Series) ^ N * MvPowerSeries.X 1 ^ n) := by
    simpa using coneSupported_svz C N n 0 hn
  have hq : ConeSupported C
      (qPochhammer (-MvPowerSeries.X 2 * (MvPowerSeries.X 0 : Series) ^ N) (MvPowerSeries.X 1) N) := by
    rw [negative_odd_monomial]
    apply coneSupported_qPochhammer_monomial
    intro j hj
    omega
  have hS : positiveSpecialization C r (MvPowerSeries.X 0 : Series) =
      (MvPowerSeries.X 0 : ChargeSeries) ^ r := by
    simpa using positiveSpecialization_svz C r 1 0 0 hr (by omega)
  have hSN : positiveSpecialization C r ((MvPowerSeries.X 0 : Series) ^ N * MvPowerSeries.X 1 ^ n) =
      (MvPowerSeries.X 0 : ChargeSeries) ^ (r * N - n) := by
    simpa using positiveSpecialization_svz C r N n 0 hr hn
  rw [mul_assoc (1 - MvPowerSeries.X 0) ((MvPowerSeries.X 0 : Series) ^ N),
    positiveSpecialization_mul C r _ _ hr (((coneSupported_one C).sub hs).mul hsn) hq,
    positiveSpecialization_mul C r _ _ hr ((coneSupported_one C).sub hs) hsn,
    positiveSpecialization_sub, positiveSpecialization_one, hS, hSN,
    positiveSpecialization_exteriorNumerator N C r hr hNC]

/-- The shifted polynomial term can use any sufficiently large common support cone. -/
theorem positiveSpecialization_finiteNumerator_shift_common (N m C r : ℕ)
    (hN : 0 < N) (hr : C + 1 < r) (hm : m - 1 + 1 ≤ C) :
    positiveSpecialization C r
      (finiteNumeratorAt N m ((MvPowerSeries.X 0 : Series) * MvPowerSeries.X 1)
        (MvPowerSeries.X 1) (MvPowerSeries.X 2)) =
      positiveSpecialization C (r - 1) (finiteNumerator N m) := by
  have hf := coneSupported_finiteNumerator N m hN
  rw [← positiveSpecialization_cone_mono (m - 1 + 1) C r _ hm
    (coneSupported_finiteNumerator_shift N m (m - 1) hf),
    positiveSpecialization_finiteNumerator_shift N m (m - 1) r (by omega) hf,
    positiveSpecialization_cone_mono (m - 1) C (r - 1) _ (by omega) hf]

/-- Positive specialization of the proved explicit-numerator recurrence. -/
theorem positiveSpecialization_finiteNumerator_recurrence (N n C r : ℕ)
    (hN : 0 < N) (hNn : N ≤ n) (hnC : n ≤ C) (hr : C + 1 < r) :
    positiveSpecialization C r (finiteNumerator N (n + 1)) =
      (1 + (MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ (r * (N + 1) - n)) *
        positiveSpecialization C r (finiteNumerator N n) -
      (((1 - (MvPowerSeries.X 0 : ChargeSeries) ^ r) * MvPowerSeries.X 0 ^ (r * N - n)) *
        ∏ j ∈ Finset.range N,
          (1 + (MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ (r * N - j))) *
        positiveSpecialization C (r - 1) (finiteNumerator N (n - N)) := by
  have hfactor := coneSupported_numeratorFactor N n C (by nlinarith)
  have hcorr := coneSupported_numeratorCorrection N n C hN (by nlinarith)
    (by have := Nat.sub_le N 1; nlinarith)
  have hnum : ConeSupported C (finiteNumerator N n) :=
    (coneSupported_finiteNumerator N n hN).mono (by omega)
  have hshift : ConeSupported C
      (finiteNumeratorAt N (n - N) ((MvPowerSeries.X 0 : Series) * MvPowerSeries.X 1)
        (MvPowerSeries.X 1) (MvPowerSeries.X 2)) :=
    (coneSupported_finiteNumerator_shift N (n - N) (n - N - 1)
      (coneSupported_finiteNumerator N (n - N) hN)).mono (by omega)
  rw [finiteNumerator_recurrence N n hNn, positiveSpecialization_sub,
    positiveSpecialization_mul C r _ _ (by omega) hfactor hnum,
    positiveSpecialization_mul C r _ _ (by omega) hcorr hshift,
    positiveSpecialization_numeratorFactor N n C r (by omega) (by nlinarith),
    positiveSpecialization_numeratorCorrection N n C r hN (by omega) (by nlinarith)
      (by have := Nat.sub_le N 1; nlinarith),
    positiveSpecialization_finiteNumerator_shift_common N (n - N) C r hN hr (by omega)]


/-- Reverse the finite exterior product to use ascending positive weights. -/
theorem descending_exterior_product_eq (N r : ℕ) :
    (∏ j ∈ Finset.range N,
      (1 + (MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ ((r + 1) * N - j))) =
      qPochhammer (-(MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ (N * r + 1))
        (MvPowerSeries.X 0) N := by
  rw [← Finset.prod_range_reflect
    (fun j => 1 + (MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ ((r + 1) * N - j)) N]
  unfold qPochhammer
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have he : (r + 1) * N - (N - 1 - j) = N * r + 1 + j := by
    rw [Nat.add_mul, one_mul, Nat.mul_comm r N]
    omega
  rw [he, pow_add]
  ring

/-- The specialized recurrence in the ascending exterior-product convention
of the auxiliary comparison sequence (ambient rank r+1, lower rank r). -/
theorem positiveSpecialization_finiteNumerator_recurrence_succ (N n C r : ℕ)
    (hN : 0 < N) (hNn : N ≤ n) (hnC : n ≤ C) (hr : C < r) :
    positiveSpecialization C (r + 1) (finiteNumerator N (n + 1)) =
      (1 + (MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ ((N + 1) * (r + 1) - n)) *
        positiveSpecialization C (r + 1) (finiteNumerator N n) -
      (((1 - (MvPowerSeries.X 0 : ChargeSeries) ^ (r + 1)) * MvPowerSeries.X 0 ^ (N * (r + 1) - n)) *
        qPochhammer (-(MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ (N * r + 1))
          (MvPowerSeries.X 0) N) *
        positiveSpecialization C r (finiteNumerator N (n - N)) := by
  have hrec := positiveSpecialization_finiteNumerator_recurrence N n C (r + 1)
    hN hNn hnC (by omega)
  rw [descending_exterior_product_eq] at hrec
  simpa only [Nat.add_sub_cancel, Nat.mul_comm] using hrec

end TorusLinkHomology.HilbertSeries
