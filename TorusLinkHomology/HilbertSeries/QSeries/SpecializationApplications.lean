import TorusLinkHomology.HilbertSeries.QSeries.SpecializationAlgebra
import TorusLinkHomology.HilbertSeries.GradedHomology

/-! Support bounds and positive specializations of the Hilbert recurrence factors. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

namespace ConeSupported

theorem zero (C : ℕ) : ConeSupported C 0 := by intro e he; simp

theorem mono {C D : ℕ} {f : Series} (hf : ConeSupported C f) (hCD : C ≤ D) :
    ConeSupported D f := by
  intro e he
  exact hf e (lt_of_le_of_lt (Nat.mul_le_mul_right _ hCD) he)

theorem add {C : ℕ} {f g : Series} (hf : ConeSupported C f) (hg : ConeSupported C g) :
    ConeSupported C (f + g) := by
  intro e he
  simp [hf e he, hg e he]

theorem neg {C : ℕ} {f : Series} (hf : ConeSupported C f) : ConeSupported C (-f) := by
  intro e he
  simp [hf e he]

theorem sub {C : ℕ} {f g : Series} (hf : ConeSupported C f) (hg : ConeSupported C g) :
    ConeSupported C (f - g) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul {C : ℕ} {f g : Series} (hf : ConeSupported C f) (hg : ConeSupported C g) :
    ConeSupported C (f * g) := by
  classical
  intro e he
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  by_cases hpf : C * p.1 0 < p.1 1
  · rw [hf _ hpf, zero_mul]
  · have hpg : C * p.2 0 < p.2 1 := by
      have h0 := congrArg (fun e => e 0) hp'
      have h1 := congrArg (fun e => e 1) hp'
      simp only [Finsupp.add_apply] at h0 h1
      nlinarith
    rw [hg _ hpg, mul_zero]

theorem pow {C : ℕ} {f : Series} (hf : ConeSupported C f) (n : ℕ) :
    ConeSupported C (f ^ n) := by
  induction n with
  | zero => simpa using coneSupported_one C
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem prod {ι : Type*} {C : ℕ} (s : Finset ι) (f : ι → Series)
    (hf : ∀ i ∈ s, ConeSupported C (f i)) : ConeSupported C (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coneSupported_one C
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem monomial (C a b h : ℕ) (q : ℚ) (hb : b ≤ C * a) :
    ConeSupported C (MvPowerSeries.monomial (tridegree a b h) q) := by
  intro e he
  rw [MvPowerSeries.coeff_monomial]
  split_ifs with heq
  · subst e
    simp only [tridegree_apply_zero, tridegree_apply_one] at he
    omega
  · rfl

end ConeSupported

theorem monomial_tridegree_one (a b h : ℕ) :
    MvPowerSeries.monomial (tridegree a b h) (1 : ℚ) =
      (MvPowerSeries.X 0 : Series) ^ a * MvPowerSeries.X 1 ^ b * MvPowerSeries.X 2 ^ h := by
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul,
    tridegree]

theorem coneSupported_svz (C a b h : ℕ) (hb : b ≤ C * a) :
    ConeSupported C ((MvPowerSeries.X 0 : Series) ^ a *
      MvPowerSeries.X 1 ^ b * MvPowerSeries.X 2 ^ h) := by
  rw [← monomial_tridegree_one]
  exact ConeSupported.monomial C a b h 1 hb

/-- The actual Hilbert series has the support cone supplied by its chain grading. -/
theorem coneSupported_hilbertSeries (N n C : ℕ) (hN : 0 < N) (hn : n - 1 ≤ C) :
    ConeSupported C (hilbertSeries N n) := by
  intro e he
  change (homologyDimension N n (e 0) (e 1) (e 2) : ℚ) = 0
  rw [homologyDimension_eq_zero_of_weight_bound hN
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ hn) he)]
  rfl

theorem positiveSpecialization_neg (C r : ℕ) (f : Series) :
    positiveSpecialization C r (-f) = -positiveSpecialization C r f := by
  have he := positiveSpecialization_add C r f (-f)
  rw [add_neg_cancel, positiveSpecialization_zero] at he
  exact eq_neg_of_add_eq_zero_right he.symm

theorem positiveSpecialization_sub (C r : ℕ) (f g : Series) :
    positiveSpecialization C r (f - g) = positiveSpecialization C r f - positiveSpecialization C r g := by
  simp only [sub_eq_add_neg, positiveSpecialization_add, positiveSpecialization_neg]

theorem positiveSpecialization_prod {ι : Type*} (C r : ℕ) (s : Finset ι) (f : ι → Series)
    (hr : C < r) (hf : ∀ i ∈ s, ConeSupported C (f i)) :
    positiveSpecialization C r (∏ i ∈ s, f i) =
      ∏ i ∈ s, positiveSpecialization C r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      positiveSpecialization_mul C r _ _ hr (hf i (Finset.mem_insert_self _ _))
        (ConeSupported.prod s f (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

theorem positiveSpecialization_svz (C r a b h : ℕ) (hr : C < r) (hb : b ≤ C * a) :
    positiveSpecialization C r ((MvPowerSeries.X 0 : Series) ^ a *
      MvPowerSeries.X 1 ^ b * MvPowerSeries.X 2 ^ h) =
      (MvPowerSeries.X 0 : ChargeSeries) ^ (r * a - b) * MvPowerSeries.X 1 ^ h := by
  rw [← monomial_tridegree_one, positiveSpecialization_monomial C r a b h 1 hr hb]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]

/-- Enlarging the support cone does not change the specialized series. -/
theorem positiveSpecialization_cone_mono (C D r : ℕ) (f : Series)
    (hCD : C ≤ D) (hf : ConeSupported C f) :
    positiveSpecialization C r f = positiveSpecialization D r f := by
  classical
  ext e
  change positiveSpecialization C r f e = positiveSpecialization D r f e
  unfold positiveSpecialization
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (Nat.mul_le_mul_right a hCD) 1))
  intro b hb hnot
  have hba : C * a < b := by
    simp only [Finset.mem_range] at hnot
    omega
  have he := hf (tridegree a b (e 1)) (by simpa using hba)
  simp [he]

private theorem monomial_mul_v_pow (a b h j : ℕ) (q : ℚ) :
    (MvPowerSeries.monomial (tridegree a b h) q : Series) * MvPowerSeries.X 1 ^ j =
      MvPowerSeries.monomial (tridegree a (b + j) h) q := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one]
  apply congrArg (fun d => (MvPowerSeries.monomial d q : Series))
  ext i
  fin_cases i <;> simp [tridegree, Finsupp.single_add]

/-- A Pochhammer product whose individual monomials lie in the support cone. -/
theorem coneSupported_qPochhammer_monomial (C a b h m : ℕ) (q : ℚ)
    (hb : ∀ j < m, b + j ≤ C * a) :
    ConeSupported C (qPochhammer (MvPowerSeries.monomial (tridegree a b h) q : Series)
      (MvPowerSeries.X 1) m) := by
  unfold qPochhammer
  apply ConeSupported.prod
  intro j hj
  rw [monomial_mul_v_pow]
  exact (coneSupported_one C).sub
    (ConeSupported.monomial C a (b + j) h q (hb j (Finset.mem_range.mp hj)))

/-- Explicit positive specialization of a finite Pochhammer product. -/
theorem positiveSpecialization_qPochhammer_monomial (C r a b h m : ℕ) (q : ℚ)
    (hr : C < r) (hb : ∀ j < m, b + j ≤ C * a) :
    positiveSpecialization C r
      (qPochhammer (MvPowerSeries.monomial (tridegree a b h) q : Series)
        (MvPowerSeries.X 1) m) =
      ∏ j ∈ Finset.range m,
        (1 - MvPowerSeries.monomial
          (Finsupp.single 0 (r * a - (b + j)) + Finsupp.single 1 h) q) := by
  unfold qPochhammer
  rw [positiveSpecialization_prod C r _ _ hr]
  · apply Finset.prod_congr rfl
    intro j hj
    rw [monomial_mul_v_pow, positiveSpecialization_sub, positiveSpecialization_one,
      positiveSpecialization_monomial C r a (b + j) h q hr (hb j (Finset.mem_range.mp hj))]
  · intro j hj
    rw [monomial_mul_v_pow]
    exact (coneSupported_one C).sub
      (ConeSupported.monomial C a (b + j) h q (hb j (Finset.mem_range.mp hj)))

theorem coneSupported_denominator (C n : ℕ) (hn : n - 1 ≤ C) :
    ConeSupported C (qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n) := by
  have he : (MvPowerSeries.X 0 : Series) = MvPowerSeries.monomial (tridegree 1 0 0) 1 := by
    simp [monomial_tridegree_one]
  rw [he]
  apply coneSupported_qPochhammer_monomial
  intro j hj
  simp only [zero_add, mul_one]
  omega

/-- Support bound for the actual normalized Hilbert series. -/
theorem coneSupported_hilbertNumerator (N n C : ℕ) (hN : 0 < N) (hn : n - 1 ≤ C) :
    ConeSupported C (qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n *
      hilbertSeries N n) :=
  (coneSupported_denominator C n hn).mul (coneSupported_hilbertSeries N n C hN hn)

theorem positiveSpecialization_denominator (C r n : ℕ) (hr : C < r) (hn : n - 1 ≤ C) :
    positiveSpecialization C r
      (qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n) =
      ∏ j ∈ Finset.range n, (1 - (MvPowerSeries.X 0 : ChargeSeries) ^ (r - j)) := by
  have he : (MvPowerSeries.X 0 : Series) = MvPowerSeries.monomial (tridegree 1 0 0) 1 := by
    simp [monomial_tridegree_one]
  rw [he, positiveSpecialization_qPochhammer_monomial C r 1 0 0 n 1 hr]
  · simp [MvPowerSeries.X_pow_eq]
  · intro j hj
    simp only [zero_add, mul_one]
    omega

end TorusLinkHomology.HilbertSeries
