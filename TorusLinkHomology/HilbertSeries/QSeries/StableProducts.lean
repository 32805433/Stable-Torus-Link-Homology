import TorusLinkHomology.HilbertSeries.AlternatingGordon

/-! Weightwise stabilization of finite q-products and the q-binomial ratio.
All limits are expressed as eventual equalities of individual coefficients. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- The q-binomial ratio as a series in an additional charge variable X. -/
def qBinomialRatio (a : ChargeSeries) : PowerSeries ChargeSeries :=
  PowerSeries.mk fun m => qPochhammer (-a) (MvPowerSeries.X 1) m * gordonDenominator m

@[simp] theorem coeff_qBinomialRatio (a : ChargeSeries) (m : ℕ) :
    PowerSeries.coeff m (qBinomialRatio a) =
      qPochhammer (-a) (MvPowerSeries.X 1) m * gordonDenominator m :=
  PowerSeries.coeff_mk _ _

theorem qBinomialRatio_step (a : ChargeSeries) :
    (1 - PowerSeries.X) * qBinomialRatio a =
      (1 + PowerSeries.C a * PowerSeries.X) *
        PowerSeries.rescale (MvPowerSeries.X 1) (qBinomialRatio a) := by
  apply PowerSeries.ext
  intro m
  rw [sub_mul, one_mul, add_mul, one_mul, mul_assoc, map_sub, map_add,
    PowerSeries.coeff_C_mul]
  cases m with
  | zero => simp [gordonDenominator]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
    simp only [PowerSeries.coeff_rescale, coeff_qBinomialRatio]
    rw [qPochhammer_succ]
    have hd := gordonDenominator_step m
    rw [pow_succ'] at hd
    linear_combination qPochhammer (-a) (MvPowerSeries.X 1) m *
      (1 + a * MvPowerSeries.X 1 ^ m) * hd

private theorem rescale_constant (t c : ChargeSeries) :
    PowerSeries.rescale t (PowerSeries.C c) = PowerSeries.C c := by
  apply PowerSeries.ext
  intro m
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with hm <;> simp [hm]

theorem qBinomialRatio_shifted_step (a t : ChargeSeries) :
    (1 - PowerSeries.C t * PowerSeries.X) * PowerSeries.rescale t (qBinomialRatio a) =
      (1 + PowerSeries.C (a * t) * PowerSeries.X) *
        PowerSeries.rescale (MvPowerSeries.X 1 * t) (qBinomialRatio a) := by
  have he := congrArg (PowerSeries.rescale t) (qBinomialRatio_step a)
  simpa only [map_mul, map_sub, map_add, map_one, PowerSeries.rescale_X,
    rescale_constant, PowerSeries.rescale_rescale, mul_assoc] using he

/-- Finite iteration of the q-binomial functional equation. -/
theorem qBinomialRatio_finite (a : ChargeSeries) (n : ℕ) :
    qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) n * qBinomialRatio a =
      qPochhammer (-PowerSeries.C a * PowerSeries.X) (PowerSeries.C (MvPowerSeries.X 1)) n *
        PowerSeries.rescale ((MvPowerSeries.X 1) ^ n) (qBinomialRatio a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qPochhammer_succ, qPochhammer_succ]
    have hs := qBinomialRatio_shifted_step a ((MvPowerSeries.X 1) ^ n)
    rw [← pow_succ'] at hs
    calc
      _ = (1 - PowerSeries.C ((MvPowerSeries.X 1) ^ n) * PowerSeries.X) *
          (qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) n * qBinomialRatio a) := by
        rw [map_pow]
        ring
      _ = _ := by
        rw [ih]
        rw [mul_left_comm, hs]
        simp only [map_mul, map_pow]
        ring

/-- The finite ratio uses the inverse with constant term one over the
coefficient ring of two-variable formal series. -/
def finiteQBinomialRatio (a : ChargeSeries) (n : ℕ) : PowerSeries ChargeSeries :=
  qPochhammer (-PowerSeries.C a * PowerSeries.X) (PowerSeries.C (MvPowerSeries.X 1)) n *
    PowerSeries.invOfUnit
      (qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) n) 1

theorem qBinomialRatio_eq_finite_mul_tail (a : ChargeSeries) (n : ℕ) :
    qBinomialRatio a = finiteQBinomialRatio a n *
      PowerSeries.rescale ((MvPowerSeries.X 1) ^ n) (qBinomialRatio a) := by
  have hi := PowerSeries.invOfUnit_mul
    (qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) n) 1
    (constantCoeff_lengthPochhammer (MvPowerSeries.X 1 : ChargeSeries) n)
  have he := congrArg (fun x => PowerSeries.invOfUnit
      (qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) n) 1 * x)
    (qBinomialRatio_finite a n)
  rw [← mul_assoc, hi, one_mul] at he
  simpa only [finiteQBinomialRatio, mul_assoc, mul_comm, mul_left_comm] using he

/-- A power of the weight variable larger than b cannot contribute at weight b. -/
theorem coeff_weight_mul_pow_eq_zero (p : ChargeSeries) (h b m : ℕ) (hm : b < m) :
    MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b)
      ((MvPowerSeries.X 1) ^ m * p) = 0 := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul]
  have hno : ¬ Finsupp.single (1 : Fin 2) m ≤ Finsupp.single 0 h + Finsupp.single 1 b := by
    intro he
    have hh := he 1
    simp at hh
    omega
  rw [if_neg hno]

/-- The finite q-binomial ratio has its stable coefficient at every weight b<n. -/
theorem coeff_finiteQBinomialRatio_stable (a : ChargeSeries) (n m h b : ℕ) (hb : b < n) :
    MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b)
      (PowerSeries.coeff m (finiteQBinomialRatio a n)) =
    MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b)
      (qPochhammer (-a) (MvPowerSeries.X 1) m * gordonDenominator m) := by
  have hp : MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b)
      (PowerSeries.coeff m (finiteQBinomialRatio a n *
        PowerSeries.rescale ((MvPowerSeries.X 1) ^ n) (qBinomialRatio a))) =
      MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b)
        (PowerSeries.coeff m (finiteQBinomialRatio a n)) := by
    rw [PowerSeries.coeff_mul, map_sum, Finset.sum_eq_single (m, 0)]
    · simp
    · intro p hp hp0
      have hsum := Finset.mem_antidiagonal.mp hp
      have hpos : 0 < p.2 := by
        by_contra hn
        have hz : p.2 = 0 := by omega
        have hfst : p.1 = m := by omega
        exact hp0 (Prod.ext hfst hz)
      rw [PowerSeries.coeff_rescale, ← pow_mul]
      rw [show PowerSeries.coeff p.1 (finiteQBinomialRatio a n) *
          ((MvPowerSeries.X 1) ^ (n * p.2) * PowerSeries.coeff p.2 (qBinomialRatio a)) =
          (MvPowerSeries.X 1) ^ (n * p.2) *
            (PowerSeries.coeff p.1 (finiteQBinomialRatio a n) *
              PowerSeries.coeff p.2 (qBinomialRatio a)) by ring]
      apply coeff_weight_mul_pow_eq_zero
      have hle : n ≤ n * p.2 := by simpa using Nat.mul_le_mul_left n hpos
      omega
    · simp
  rw [← qBinomialRatio_eq_finite_mul_tail, coeff_qBinomialRatio] at hp
  exact hp.symm

/-- A finite product whose first weight is r differs from one by a multiple
of v^r, over an arbitrary commutative coefficient ring. -/
theorem qPochhammer_pow_sub_one {S : Type*} [CommRing S] (v : S) (r n : ℕ) :
    ∃ p : S, qPochhammer (v ^ r) v n = 1 + v ^ r * p := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p - v ^ n - v ^ r * p * v ^ n, ?_⟩
    rw [qPochhammer_succ, hp]
    ring

/-- Gaussian binomials as quotients of finite products, in a ring where
all q-factorial denominators are invertible. -/
theorem gaussianBinomial_eq_product (n i : ℕ) (hi : i ≤ n) :
    gaussianBinomial (MvPowerSeries.X 1 : ChargeSeries) n i =
      qPochhammer (MvPowerSeries.X 1 ^ (n - i + 1)) (MvPowerSeries.X 1) i *
        gordonDenominator i := by
  induction n generalizing i with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      by_cases he : i = n
      · subst i
        rw [gaussianBinomial_self]
        simp only [Nat.sub_self, zero_add, pow_one, gordonDenominator]
        symm
        exact qPochhammer_mul_inv _ _ (by simp) _
      · have hin : i + 1 ≤ n := by omega
        rw [gaussianBinomial, ih (i + 1) hin, ih i (by omega)]
        have hleft : n - (i + 1) + 1 = n - i := by omega
        have hright : n + 1 - (i + 1) + 1 = n - i + 1 := by omega
        rw [hleft, hright, qPochhammer_shift, qPochhammer_succ]
        rw [← pow_succ, ← gordonDenominator_step i]
        ring

/-- The Gaussian binomial has stabilized at weight b once its upper index
is at least i+b. This includes i=0 and b=0. -/
theorem coeff_gaussianBinomial_stable (n i h b : ℕ) (hb : i + b ≤ n) :
    MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b)
      (gaussianBinomial (MvPowerSeries.X 1 : ChargeSeries) n i) =
    MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b) (gordonDenominator i) := by
  rw [gaussianBinomial_eq_product n i (by omega)]
  obtain ⟨p, hp⟩ := qPochhammer_pow_sub_one (MvPowerSeries.X 1 : ChargeSeries) (n - i + 1) i
  rw [hp, add_mul, one_mul, map_add, mul_assoc,
    coeff_weight_mul_pow_eq_zero (p * gordonDenominator i) h b (n - i + 1) (by omega)]
  simp

private theorem chargeIndex_eq (e : Fin 2 →₀ ℕ) :
    Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) = e := by
  ext i
  fin_cases i <;> simp

theorem coeff_finiteQBinomialRatio_stable_at (a : ChargeSeries) (n m : ℕ)
    (e : Fin 2 →₀ ℕ) (he : e 1 < n) :
    MvPowerSeries.coeff e (PowerSeries.coeff m (finiteQBinomialRatio a n)) =
      MvPowerSeries.coeff e (qPochhammer (-a) (MvPowerSeries.X 1) m * gordonDenominator m) := by
  simpa only [chargeIndex_eq] using coeff_finiteQBinomialRatio_stable a n m (e 0) (e 1) he

theorem coeff_gaussianBinomial_stable_at (n i : ℕ) (e : Fin 2 →₀ ℕ) (he : i + e 1 ≤ n) :
    MvPowerSeries.coeff e (gaussianBinomial (MvPowerSeries.X 1 : ChargeSeries) n i) =
      MvPowerSeries.coeff e (gordonDenominator i) := by
  simpa only [chargeIndex_eq] using coeff_gaussianBinomial_stable n i (e 0) (e 1) he

/-- Agreement below a weight cutoff is preserved by multiplication by an
arbitrary two-variable series. No bound on its charge degree is needed. -/
theorem coeff_mul_of_weight_congr (p f g : ChargeSeries) (n : ℕ)
    (hfg : ∀ e : Fin 2 →₀ ℕ, e 1 < n → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g)
    (e : Fin 2 →₀ ℕ) (he : e 1 < n) :
    MvPowerSeries.coeff e (p * f) = MvPowerSeries.coeff e (p * g) := by
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro q hq
  have hsum := Finset.mem_antidiagonal.mp hq
  have hh := congrArg (fun x : Fin 2 →₀ ℕ => x 1) hsum
  simp only [Finsupp.add_apply] at hh
  rw [hfg q.2 (by omega)]

theorem coeff_mul_finiteQBinomialRatio_stable (p a : ChargeSeries) (n m : ℕ)
    (e : Fin 2 →₀ ℕ) (he : e 1 < n) :
    MvPowerSeries.coeff e (p * PowerSeries.coeff m (finiteQBinomialRatio a n)) =
      MvPowerSeries.coeff e
        (p * (qPochhammer (-a) (MvPowerSeries.X 1) m * gordonDenominator m)) :=
  coeff_mul_of_weight_congr p _ _ n (coeff_finiteQBinomialRatio_stable_at a n m) e he

theorem coeff_mul_gaussianBinomial_stable (p : ChargeSeries) (n i : ℕ)
    (e : Fin 2 →₀ ℕ) (he : i + e 1 ≤ n) :
    MvPowerSeries.coeff e (p * gaussianBinomial (MvPowerSeries.X 1 : ChargeSeries) n i) =
      MvPowerSeries.coeff e (p * gordonDenominator i) := by
  apply coeff_mul_of_weight_congr p _ _ (n - i + 1) ?_ e (by omega)
  intro d hd
  exact coeff_gaussianBinomial_stable_at n i d (by omega)

/-- Shifting the numerator parameter by v cancels the factor 1-X.
This is the coefficient identity used by all correction indices at least two. -/
theorem qBinomialRatio_parameter_shift (a : ChargeSeries) :
    (1 - PowerSeries.X) * qBinomialRatio (a * MvPowerSeries.X 1) =
      PowerSeries.rescale (MvPowerSeries.X 1) (qBinomialRatio a) := by
  apply PowerSeries.ext
  intro m
  rw [sub_mul, one_mul, map_sub]
  cases m with
  | zero => simp
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp only [PowerSeries.coeff_rescale, coeff_qBinomialRatio]
    rw [qPochhammer_succ, qPochhammer_shift, ← gordonDenominator_step m]
    simp only [neg_mul, pow_succ', sub_neg_eq_add]
    ring

theorem coeff_weight_mul_pow_eq_zero_at (p : ChargeSeries) (e : Fin 2 →₀ ℕ)
    (m : ℕ) (he : e 1 < m) :
    MvPowerSeries.coeff e ((MvPowerSeries.X 1) ^ m * p) = 0 := by
  simpa only [chargeIndex_eq] using coeff_weight_mul_pow_eq_zero p (e 0) (e 1) m he

/-- Every nonconstant term of a product with parameter divisible by t is divisible by t. -/
theorem qPochhammer_scaled_sub_one {S : Type*} [CommRing S] (a v t : S) (n : ℕ) :
    ∃ p : S, qPochhammer (a * t) v n = 1 + t * p := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p - a * v ^ n - a * t * p * v ^ n, ?_⟩
    rw [qPochhammer_succ, hp]
    ring

/-- Extending a finite numerator product changes no coefficient below its
first omitted weight, even after multiplication by an arbitrary length series. -/
theorem coeff_mul_lengthPochhammer_extend (a : ChargeSeries) (p : PowerSeries ChargeSeries)
    (n d m : ℕ) (e : Fin 2 →₀ ℕ) (he : e 1 < n) :
    MvPowerSeries.coeff e (PowerSeries.coeff m
      (p * qPochhammer (-PowerSeries.C a * PowerSeries.X)
        (PowerSeries.C (MvPowerSeries.X 1)) (n + d))) =
    MvPowerSeries.coeff e (PowerSeries.coeff m
      (p * qPochhammer (-PowerSeries.C a * PowerSeries.X)
        (PowerSeries.C (MvPowerSeries.X 1)) n)) := by
  obtain ⟨q, hq⟩ := qPochhammer_scaled_sub_one
    (-PowerSeries.C a * PowerSeries.X) (PowerSeries.C (MvPowerSeries.X 1))
    ((PowerSeries.C (MvPowerSeries.X 1)) ^ n) d
  have hex : p * qPochhammer (-PowerSeries.C a * PowerSeries.X)
        (PowerSeries.C (MvPowerSeries.X 1)) (n + d) =
      p * qPochhammer (-PowerSeries.C a * PowerSeries.X)
        (PowerSeries.C (MvPowerSeries.X 1)) n +
      PowerSeries.C ((MvPowerSeries.X 1) ^ n) *
        (p * qPochhammer (-PowerSeries.C a * PowerSeries.X)
          (PowerSeries.C (MvPowerSeries.X 1)) n * q) := by
    rw [qPochhammer_add, hq, map_pow]
    ring
  rw [hex, map_add, map_add, PowerSeries.coeff_C_mul,
    coeff_weight_mul_pow_eq_zero_at _ e n he, add_zero]

theorem coeff_mul_lengthPochhammer_lengths (a : ChargeSeries) (p : PowerSeries ChargeSeries)
    (n₁ n₂ m : ℕ) (e : Fin 2 →₀ ℕ) (h₁ : e 1 < n₁) (h₂ : e 1 < n₂) :
    MvPowerSeries.coeff e (PowerSeries.coeff m
      (p * qPochhammer (-PowerSeries.C a * PowerSeries.X)
        (PowerSeries.C (MvPowerSeries.X 1)) n₁)) =
    MvPowerSeries.coeff e (PowerSeries.coeff m
      (p * qPochhammer (-PowerSeries.C a * PowerSeries.X)
        (PowerSeries.C (MvPowerSeries.X 1)) n₂)) := by
  rcases le_total n₁ n₂ with hle | hle
  · have he := coeff_mul_lengthPochhammer_extend a p n₁ (n₂ - n₁) m e h₁
    simpa only [Nat.add_sub_of_le hle] using he.symm
  · have he := coeff_mul_lengthPochhammer_extend a p n₂ (n₁ - n₂) m e h₂
    simpa only [Nat.add_sub_of_le hle] using he

/-- Finite numerator and denominator truncations may have different lengths. -/
def finiteQBinomialRatioLengths (a : ChargeSeries) (m n : ℕ) : PowerSeries ChargeSeries :=
  qPochhammer (-PowerSeries.C a * PowerSeries.X) (PowerSeries.C (MvPowerSeries.X 1)) m *
    PowerSeries.invOfUnit
      (qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) n) 1

theorem coeff_finiteQBinomialRatioLengths_stable (a : ChargeSeries) (n₁ n₂ m : ℕ)
    (e : Fin 2 →₀ ℕ) (h₁ : e 1 < n₁) (h₂ : e 1 < n₂) :
    MvPowerSeries.coeff e (PowerSeries.coeff m (finiteQBinomialRatioLengths a n₁ n₂)) =
      MvPowerSeries.coeff e (PowerSeries.coeff m (qBinomialRatio a)) := by
  have he := coeff_mul_lengthPochhammer_lengths a
    (PowerSeries.invOfUnit (qPochhammer PowerSeries.X (PowerSeries.C (MvPowerSeries.X 1)) n₂) 1)
    n₁ n₂ m e h₁ h₂
  have he' := coeff_finiteQBinomialRatio_stable_at a n₂ m e h₂
  rw [← coeff_qBinomialRatio] at he'
  apply Eq.trans _ he'
  simpa only [finiteQBinomialRatioLengths, finiteQBinomialRatio, mul_comm] using he

/-- Weight agreement of length series survives arbitrary multiplication. -/
theorem coeff_length_mul_of_weight_congr (p f g : PowerSeries ChargeSeries) (n : ℕ)
    (hfg : ∀ m (e : Fin 2 →₀ ℕ), e 1 < n →
      MvPowerSeries.coeff e (PowerSeries.coeff m f) = MvPowerSeries.coeff e (PowerSeries.coeff m g))
    (m : ℕ) (e : Fin 2 →₀ ℕ) (he : e 1 < n) :
    MvPowerSeries.coeff e (PowerSeries.coeff m (p * f)) =
      MvPowerSeries.coeff e (PowerSeries.coeff m (p * g)) := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact coeff_mul_of_weight_congr _ _ _ n (hfg q.2) e he

end TorusLinkHomology.HilbertSeries
