import TorusLinkHomology.HilbertSeries.QSeries

/-! Finite coefficient sums for positive-weight specialization and their separation property. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- A coefficient of s^a v^b z^h. -/
def tridegree (a b h : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 h

@[simp] theorem tridegree_apply_zero (a b h : ℕ) : tridegree a b h 0 = a := by
  simp [tridegree]
@[simp] theorem tridegree_apply_one (a b h : ℕ) : tridegree a b h 1 = b := by
  simp [tridegree]
@[simp] theorem tridegree_apply_two (a b h : ℕ) : tridegree a b h 2 = h := by
  simp [tridegree]
@[simp] theorem tridegree_eta (e : Fin 3 →₀ ℕ) : tridegree (e 0) (e 1) (e 2) = e := by
  ext i
  fin_cases i <;> simp

/-- Coefficients after s^a v^b z^h ↦ w^(ra-b) z^h, on the support cone b≤Ca.
For r>C any contributing a is at most the target weight w, so the sums are finite. -/
def positiveSpecialization (C r : ℕ) (f : Series) : MvPowerSeries (Fin 2) ℚ :=
  fun e => ∑ a ∈ Finset.range (e 0 + 1), ∑ b ∈ Finset.range (C * a + 1),
    if r * a - b = e 0 then MvPowerSeries.coeff (tridegree a b (e 1)) f else 0

theorem positiveSpecialization_add (C r : ℕ) (f g : Series) :
    positiveSpecialization C r (f + g) = positiveSpecialization C r f + positiveSpecialization C r g := by
  ext e
  change positiveSpecialization C r (f + g) e =
    positiveSpecialization C r f e + positiveSpecialization C r g e
  simp only [positiveSpecialization]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp

/-- The chosen steep specialization recovers one coefficient exactly. -/
theorem positiveSpecialization_coeff (C r a b h : ℕ) (f : Series)
    (hb : b ≤ C * a) (hr : C * (a + 1) < r) :
    MvPowerSeries.coeff (Finsupp.single 0 (r * a - b) + Finsupp.single 1 h)
      (positiveSpecialization C r f) = MvPowerSeries.coeff (tridegree a b h) f := by
  classical
  simp only [MvPowerSeries.coeff_apply, positiveSpecialization, Finsupp.add_apply,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero, zero_add]
  have hCa : C < r := by nlinarith
  have ha : a ≤ r * a - b := by
    have hp := Nat.mul_le_mul_right a (show C + 1 ≤ r by omega)
    rw [Nat.add_mul, one_mul] at hp
    omega
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro b' hb' hne
      apply if_neg
      intro he
      have hh := specialization_degree_separation hb
        (show b' ≤ C * a by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hb') hr he.symm
      exact hne hh.2.symm
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  · intro a' ha' hne
    apply Finset.sum_eq_zero
    intro b' hb'
    apply if_neg
    intro he
    have hh := specialization_degree_separation hb
      (show b' ≤ C * a' by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hb') hr he.symm
    exact hne hh.1.symm
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

/-- Equality after all sufficiently steep substitutions determines a series
supported in the common cone. No polynomiality assumption is used. -/
theorem eq_of_positiveSpecialization_eq (C : ℕ) {f g : Series}
    (hf : ∀ e, C * e 0 < e 1 → MvPowerSeries.coeff e f = 0)
    (hg : ∀ e, C * e 0 < e 1 → MvPowerSeries.coeff e g = 0)
    (he : ∃ R : ℕ, ∀ r, R ≤ r → positiveSpecialization C r f = positiveSpecialization C r g) :
    f = g := by
  obtain ⟨R, hR⟩ := he
  ext e
  by_cases hb : e 1 ≤ C * e 0
  · let r := C * (e 0 + 1) + R + 1
    have hr : C * (e 0 + 1) < r := by omega
    have heq := congrArg (MvPowerSeries.coeff
      (Finsupp.single 0 (r * e 0 - e 1) + Finsupp.single 1 (e 2)))
      (hR r (by omega))
    simpa only [positiveSpecialization_coeff C r (e 0) (e 1) (e 2) f hb hr,
      positiveSpecialization_coeff C r (e 0) (e 1) (e 2) g hb hr, tridegree_eta] using heq
  · rw [hf e (by omega), hg e (by omega)]

end TorusLinkHomology.HilbertSeries
