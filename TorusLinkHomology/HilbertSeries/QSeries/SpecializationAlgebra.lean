import TorusLinkHomology.HilbertSeries.QSeries.Specialization
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-! Algebraic compatibility of positive-weight specialization on a support cone. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- The finite fiber of the positive weight map on the support cone. -/
def specializationFiber (C r w : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (w + 1)) ×ˢ (Finset.range (C * w + 1))).filter
    (fun p => p.2 ≤ C * p.1 ∧ r * p.1 - p.2 = w)

private theorem cone_le_weight {C r a b : ℕ} (hr : C < r) (hb : b ≤ C * a) :
    a ≤ r * a - b := by
  have := Nat.mul_le_mul_right a (show C + 1 ≤ r by omega)
  rw [Nat.add_mul, one_mul] at this
  omega

@[simp] theorem mem_specializationFiber {C r w a b : ℕ} (hr : C < r) :
    (a, b) ∈ specializationFiber C r w ↔ b ≤ C * a ∧ r * a - b = w := by
  simp only [specializationFiber, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  constructor
  · exact fun h => h.2
  · rintro ⟨hb, he⟩
    have ha : a ≤ w := he ▸ cone_le_weight hr hb
    have hbw := hb.trans (Nat.mul_le_mul_left C ha)
    exact ⟨⟨by omega, by omega⟩, hb, he⟩

/-- A coefficient is a sum over the finite fiber of the weight map. -/
theorem positiveSpecialization_coeff_fiber (C r w h : ℕ) (f : Series) :
    positiveSpecialization C r f (Finsupp.single 0 w + Finsupp.single 1 h) =
      ∑ p ∈ specializationFiber C r w, MvPowerSeries.coeff (tridegree p.1 p.2 h) f := by
  classical
  simp only [positiveSpecialization, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero, zero_add,
    specializationFiber, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≤ w := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ha
  symm
  calc
    (∑ b ∈ Finset.range (C * w + 1),
        if b ≤ C * a ∧ r * a - b = w then MvPowerSeries.coeff (tridegree a b h) f else 0) =
      ∑ b ∈ Finset.range (C * a + 1),
        if b ≤ C * a ∧ r * a - b = w then MvPowerSeries.coeff (tridegree a b h) f else 0 := by
          symm
          apply Finset.sum_subset (Finset.range_mono (by nlinarith))
          intro b hb hba
          have hb' : ¬b ≤ C * a := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hba
          simp [hb']
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' : b ≤ C * a := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hb
      simp [hb']

@[simp] theorem tridegree_le_tridegree (a b h a' b' h' : ℕ) :
    tridegree a b h ≤ tridegree a' b' h' ↔ a ≤ a' ∧ b ≤ b' ∧ h ≤ h' := by
  constructor
  · intro he
    exact ⟨by simpa using he 0, by simpa using he 1, by simpa using he 2⟩
  · rintro ⟨ha, hb, hh⟩ i
    fin_cases i <;> simpa using (by assumption)

@[simp] theorem tridegree_sub (a b h a' b' h' : ℕ) :
    tridegree a b h - tridegree a' b' h' = tridegree (a - a') (b - b') (h - h') := by
  ext i
  fin_cases i <;> simp [Finsupp.tsub_apply]

/-- Being supported in the cone used by positive specialization. -/
def ConeSupported (C : ℕ) (f : Series) : Prop :=
  ∀ e, C * e 0 < e 1 → MvPowerSeries.coeff e f = 0

private theorem cone_coeff {C : ℕ} {f : Series} (hf : ConeSupported C f)
    {a b h : ℕ} (he : MvPowerSeries.coeff (tridegree a b h) f ≠ 0) : b ≤ C * a := by
  by_contra hb
  exact he (hf _ (by simpa using (Nat.lt_of_not_ge hb)))

private theorem weight_add {C r a b a' b' : ℕ} (hr : C < r)
    (hb : b ≤ C * a) (hb' : b' ≤ C * a') :
    r * (a + a') - (b + b') = (r * a - b) + (r * a' - b') := by
  have hba := hb.trans (Nat.mul_le_mul_right a (Nat.le_of_lt hr))
  have hba' := hb'.trans (Nat.mul_le_mul_right a' (Nat.le_of_lt hr))
  rw [Nat.mul_add]
  omega

private theorem monomial_mul_coeff_data {C a b h A B H : ℕ} {q : ℚ} {f : Series}
    (hf : ConeSupported C f)
    (hp : MvPowerSeries.coeff (tridegree A B H)
      (MvPowerSeries.monomial (tridegree a b h) q * f) ≠ 0) :
    (a ≤ A ∧ b ≤ B ∧ h ≤ H) ∧ B - b ≤ C * (A - a) := by
  simp only [MvPowerSeries.coeff_monomial_mul, tridegree_le_tridegree] at hp
  split_ifs at hp with he
  · rw [tridegree_sub] at hp
    exact ⟨he, cone_coeff hf (right_ne_zero_of_mul hp)⟩
  · exact (hp rfl).elim

private theorem shifted_weight {C r a b A B : ℕ} (hr : C < r)
    (hb : b ≤ C * a) (ha : a ≤ A) (hbB : b ≤ B) (hrem : B - b ≤ C * (A - a)) :
    r * A - B = (r * a - b) + (r * (A - a) - (B - b)) := by
  have he := weight_add hr hb hrem
  have ha' : a + (A - a) = A := by omega
  have hb' : b + (B - b) = B := by omega
  rwa [ha', hb'] at he

/-- Multiplication by a supported monomial commutes with positive specialization.
This is the polynomial multiplication law needed when clearing denominators. -/
theorem positiveSpecialization_monomial_mul (C r a b h : ℕ) (q : ℚ) (f : Series)
    (hr : C < r) (hb : b ≤ C * a) (hf : ConeSupported C f) :
    positiveSpecialization C r (MvPowerSeries.monomial (tridegree a b h) q * f) =
      MvPowerSeries.monomial (Finsupp.single 0 (r * a - b) + Finsupp.single 1 h) q *
        positiveSpecialization C r f := by
  classical
  ext e
  obtain ⟨w, H, rfl⟩ : ∃ w H, e = Finsupp.single 0 w + Finsupp.single 1 H := by
    refine ⟨e 0, e 1, ?_⟩
    ext i
    fin_cases i <;> simp
  rw [MvPowerSeries.coeff_monomial_mul]
  have hle : (Finsupp.single (0 : Fin 2) (r * a - b) + Finsupp.single 1 h ≤
      Finsupp.single 0 w + Finsupp.single 1 H) ↔ r * a - b ≤ w ∧ h ≤ H := by
    constructor
    · intro he
      exact ⟨by simpa using he 0, by simpa using he 1⟩
    · rintro ⟨hw, hh⟩ i
      fin_cases i
      · simpa using hw
      · simpa using hh
  simp only [hle]
  change positiveSpecialization C r _ _ = _
  rw [positiveSpecialization_coeff_fiber]
  by_cases hwh : r * a - b ≤ w ∧ h ≤ H
  · rw [if_pos hwh]
    have he : (Finsupp.single (0 : Fin 2) w + Finsupp.single 1 H) -
        (Finsupp.single 0 (r * a - b) + Finsupp.single 1 h) =
        Finsupp.single 0 (w - (r * a - b)) + Finsupp.single 1 (H - h) := by
      ext i
      fin_cases i <;> simp [Finsupp.tsub_apply]
    rw [he, MvPowerSeries.coeff_apply, positiveSpecialization_coeff_fiber, Finset.mul_sum]
    symm
    apply Finset.sum_bij_ne_zero
      (fun p _ _ => (a + p.1, b + p.2))
    · intro p hp hp0
      obtain ⟨hpcone, hpweight⟩ := (mem_specializationFiber hr).mp hp
      apply (mem_specializationFiber hr).mpr
      constructor
      · nlinarith
      · rw [weight_add hr hb hpcone, hpweight]
        omega
    · intro p hp hp0 p' hp' hp0' heq
      have ha := congrArg Prod.fst heq
      have hb' := congrArg Prod.snd heq
      exact Prod.ext (by simpa using ha) (by simpa using hb')
    · intro p hp hp0
      obtain ⟨hpcone, hpweight⟩ := (mem_specializationFiber hr).mp hp
      obtain ⟨⟨ha, hb', hh⟩, hrem⟩ := monomial_mul_coeff_data hf hp0
      have hw := shifted_weight hr hb ha hb' hrem
      refine ⟨(p.1 - a, p.2 - b), ?_, ?_, ?_⟩
      · apply (mem_specializationFiber hr).mpr
        exact ⟨hrem, by omega⟩
      · simpa only [MvPowerSeries.coeff_monomial_mul, tridegree_le_tridegree,
          if_pos (show a ≤ p.1 ∧ b ≤ p.2 ∧ h ≤ H from ⟨ha, hb', hh⟩), tridegree_sub] using hp0
      · apply Prod.ext <;> simp only <;> omega
    · intro p hp hp0
      simp only [MvPowerSeries.coeff_monomial_mul, tridegree_le_tridegree,
        Nat.le_add_right, true_and, if_pos hwh.2, tridegree_sub,
        Nat.add_sub_cancel_left]
  · rw [if_neg hwh]
    apply Finset.sum_eq_zero
    intro p hp
    by_contra hp0
    obtain ⟨hpcone, hpweight⟩ := (mem_specializationFiber hr).mp hp
    obtain ⟨⟨ha, hb', hh⟩, hrem⟩ := monomial_mul_coeff_data hf hp0
    have hw := shifted_weight hr hb ha hb' hrem
    exact hwh ⟨by omega, hh⟩

@[simp] theorem positiveSpecialization_zero (C r : ℕ) :
    positiveSpecialization C r 0 = 0 := by
  ext e
  change positiveSpecialization C r 0 e = 0
  simp [positiveSpecialization]

@[simp] theorem tridegree_eq_zero (a b h : ℕ) :
    tridegree a b h = 0 ↔ a = 0 ∧ b = 0 ∧ h = 0 := by
  constructor
  · intro he
    exact ⟨by simpa using congrArg (fun e => e 0) he,
      by simpa using congrArg (fun e => e 1) he,
      by simpa using congrArg (fun e => e 2) he⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp [tridegree]

@[simp] theorem positiveSpecialization_one (C r : ℕ) :
    positiveSpecialization C r 1 = 1 := by
  classical
  ext e
  have he : e = 0 ↔ e 0 = 0 ∧ e 1 = 0 := by
    constructor
    · rintro rfl; simp
    · rintro ⟨ha, hb⟩
      ext i
      fin_cases i <;> assumption
  change positiveSpecialization C r 1 e = MvPowerSeries.coeff e 1
  simp only [positiveSpecialization, MvPowerSeries.coeff_one, tridegree_eq_zero]
  rw [Finset.sum_eq_single 0]
  · simp [he, ite_and, eq_comm]
  · intro a ha hne
    apply Finset.sum_eq_zero
    intro b hb
    simp [hne]
  · simp

theorem positiveSpecialization_sum {ι : Type*} (C r : ℕ) (s : Finset ι) (f : ι → Series) :
    positiveSpecialization C r (∑ i ∈ s, f i) = ∑ i ∈ s, positiveSpecialization C r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, positiveSpecialization_add, ih]

theorem coneSupported_one (C : ℕ) : ConeSupported C 1 := by
  intro e he
  rw [MvPowerSeries.coeff_one, if_neg]
  intro hz
  subst e
  simp at he

/-- A supported monomial maps to its expected nonnegative weight. -/
theorem positiveSpecialization_monomial (C r a b h : ℕ) (q : ℚ)
    (hr : C < r) (hb : b ≤ C * a) :
    positiveSpecialization C r (MvPowerSeries.monomial (tridegree a b h) q) =
      MvPowerSeries.monomial (Finsupp.single 0 (r * a - b) + Finsupp.single 1 h) q := by
  simpa using positiveSpecialization_monomial_mul C r a b h q 1 hr hb (coneSupported_one C)

/-- Specialization respects multiplication by any polynomial supported in the cone. -/
theorem positiveSpecialization_polynomial_mul (C r : ℕ) (p : MvPolynomial (Fin 3) ℚ)
    (f : Series) (hr : C < r) (hp : ConeSupported C (p : Series)) (hf : ConeSupported C f) :
    positiveSpecialization C r ((p : Series) * f) =
      positiveSpecialization C r (p : Series) * positiveSpecialization C r f := by
  classical
  have hpoly : (p : Series) = ∑ e ∈ p.support, MvPowerSeries.monomial e (p.coeff e) := by
    simpa only [map_sum, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      MvPolynomial.coe_monomial] using congrArg
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 3) (R := ℚ)) p.as_sum
  rw [hpoly, Finset.sum_mul, positiveSpecialization_sum, positiveSpecialization_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  have hb : e 1 ≤ C * e 0 := by
    by_contra hb
    have hz := hp e (by omega)
    exact (MvPolynomial.mem_support_iff.mp he) hz
  rw [← tridegree_eta e, positiveSpecialization_monomial_mul C r _ _ _ _ _ hr hb hf,
    positiveSpecialization_monomial C r _ _ _ _ hr hb]

/-- Coefficients of a product only depend on coefficients below the target degree. -/
private theorem coeff_mul_congr_left {σ : Type*} (e : σ →₀ ℕ)
    (f f' g : MvPowerSeries σ ℚ)
    (hf : ∀ d ≤ e, MvPowerSeries.coeff d f = MvPowerSeries.coeff d f') :
    MvPowerSeries.coeff e (f * g) = MvPowerSeries.coeff e (f' * g) := by
  classical
  simp only [MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he := Finset.mem_antidiagonal.mp hp
  rw [hf p.1 (by rw [← he]; exact le_self_add)]

/-- A finite coefficient box suffices to determine a specialized coefficient. -/
private theorem specialization_coeff_congr (C r w H : ℕ) (f g : Series)
    (he : ∀ d ≤ tridegree w (C * w) H,
      MvPowerSeries.coeff d f = MvPowerSeries.coeff d g) :
    positiveSpecialization C r f (Finsupp.single 0 w + Finsupp.single 1 H) =
      positiveSpecialization C r g (Finsupp.single 0 w + Finsupp.single 1 H) := by
  rw [positiveSpecialization_coeff_fiber, positiveSpecialization_coeff_fiber]
  apply Finset.sum_congr rfl
  intro p hp
  have hbounds := (Finset.mem_filter.mp hp).1
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hbounds
  apply he
  rw [tridegree_le_tridegree]
  exact ⟨by simpa only [Finset.mem_range, Nat.lt_succ_iff] using ha,
    by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hb, le_rfl⟩

/-- Positive specialization is multiplicative on a common support cone.
Only a finite coefficient box of the first factor is needed at each target. -/
theorem positiveSpecialization_mul (C r : ℕ) (f g : Series) (hr : C < r)
    (hf : ConeSupported C f) (hg : ConeSupported C g) :
    positiveSpecialization C r (f * g) =
      positiveSpecialization C r f * positiveSpecialization C r g := by
  classical
  ext e
  obtain ⟨w, H, rfl⟩ : ∃ w H, e = Finsupp.single 0 w + Finsupp.single 1 H := by
    refine ⟨e 0, e 1, ?_⟩
    ext i
    fin_cases i <;> simp
  let cap := tridegree w (C * w) H
  let p := MvPowerSeries.truncFinset ℚ (Finset.Iic cap) f
  have hpcoeff (d : Fin 3 →₀ ℕ) (hd : d ≤ cap) :
      MvPowerSeries.coeff d (p : Series) = MvPowerSeries.coeff d f := by
    exact MvPowerSeries.coeff_truncFinset_of_mem f (Finset.mem_Iic.mpr hd)
  have hp : ConeSupported C (p : Series) := by
    intro d hd
    change p.coeff d = 0
    rw [MvPowerSeries.coeff_truncFinset]
    split_ifs <;> simp [hf d hd]
  have hleft : positiveSpecialization C r ((p : Series) * g)
        (Finsupp.single 0 w + Finsupp.single 1 H) =
      positiveSpecialization C r (f * g) (Finsupp.single 0 w + Finsupp.single 1 H) := by
    apply specialization_coeff_congr
    intro d hd
    exact coeff_mul_congr_left d _ _ g (fun d' hd' => hpcoeff d' (hd'.trans hd))
  have hright : MvPowerSeries.coeff (Finsupp.single 0 w + Finsupp.single 1 H)
        (positiveSpecialization C r (p : Series) * positiveSpecialization C r g) =
      MvPowerSeries.coeff (Finsupp.single 0 w + Finsupp.single 1 H)
        (positiveSpecialization C r f * positiveSpecialization C r g) := by
    apply coeff_mul_congr_left
    intro d hd
    have hd0 : d 0 ≤ w := by simpa using hd 0
    have hd1 : d 1 ≤ H := by simpa using hd 1
    have heta : d = Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) := by
      ext i
      fin_cases i <;> simp
    rw [heta]
    change positiveSpecialization C r (p : Series) _ = positiveSpecialization C r f _
    apply specialization_coeff_congr
    intro d' hd'
    apply hpcoeff
    apply hd'.trans
    rw [tridegree_le_tridegree]
    exact ⟨hd0, Nat.mul_le_mul_left C hd0, hd1⟩
  change positiveSpecialization C r (f * g) _ = _
  rw [← hleft, positiveSpecialization_polynomial_mul C r p g hr hp hg]
  exact hright

end TorusLinkHomology.HilbertSeries
