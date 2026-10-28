import TorusLinkHomology.HilbertSeries.InitialSeries
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-! The passive monomial enumerator in general reversal, with arbitrary
exterior weight offset. All coefficient sums are finite by positive weights. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries.GeneralReversal

/-- Polynomial weights are 1,...,p; exterior weights are K+1,...,K+p. -/
def enumeratorWeight (K : ℕ) {p : ℕ} (t : ChainIndex p) : ℕ :=
  (∑ i : Fin p, (i.val + 1) * t.1 i) + ∑ i ∈ t.2, (K + i.val + 1)

/-- The actual number of passive monomials in each weight and exterior degree. -/
def passiveEnumerator (K p : ℕ) : ChargeSeries :=
  fun e => (Nat.card {t : ChainIndex p // enumeratorWeight K t = e 0 ∧ t.2.card = e 1} : ℚ)

/-- Inclusion of bounded polynomial exponents in unrestricted passive indices. -/
def boundedPassiveIndex (p A : ℕ) (m : BoundedMonomial p A) : ChainIndex p :=
  (Finsupp.equivFunOnFinite.symm (fun i => (m.1 i).val), m.2)

theorem exponent_le_enumeratorWeight (K p : ℕ) (t : ChainIndex p) (i : Fin p) :
    t.1 i ≤ enumeratorWeight K t := by
  have hi : t.1 i ≤ (i.val + 1) * t.1 i := by nlinarith
  have hs : (i.val + 1) * t.1 i ≤ ∑ j : Fin p, (j.val + 1) * t.1 j :=
    Finset.single_le_sum (f := fun j : Fin p => (j.val + 1) * t.1 j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact hi.trans (hs.trans (Nat.le_add_right _ _))

/-- The finite bound A loses no monomial of weight at most A. -/
def passiveFiberEquiv (K p A w h : ℕ) (hw : w ≤ A) :
    {t : ChainIndex p // enumeratorWeight K t = w ∧ t.2.card = h} ≃
      {m : BoundedMonomial p A //
        enumeratorWeight K (boundedPassiveIndex p A m) = w ∧ m.2.card = h} where
  toFun t := ⟨(fun i => ⟨t.val.1 i, Nat.lt_succ_of_le
    ((exponent_le_enumeratorWeight K p t.val i).trans (t.property.1.trans_le hw))⟩, t.val.2),
    by simpa only [enumeratorWeight, boundedPassiveIndex, Finsupp.coe_equivFunOnFinite_symm] using t.property⟩
  invFun m := ⟨boundedPassiveIndex p A m.val, m.property⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      simp [boundedPassiveIndex]
    · rfl
  right_inv m := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply Fin.ext
      simp [boundedPassiveIndex]
    · rfl

/-- Every fixed passive weight/exterior-degree fiber is finite. -/
instance passiveEnumeratorFiber_finite (K p w h : ℕ) :
    Finite {t : ChainIndex p // enumeratorWeight K t = w ∧ t.2.card = h} :=
  Finite.of_equiv _ (passiveFiberEquiv K p w w h le_rfl).symm

@[simp] theorem coeff_passiveEnumerator (K p : ℕ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (passiveEnumerator K p) =
      (Nat.card {t : ChainIndex p // enumeratorWeight K t = e 0 ∧ t.2.card = e 1} : ℚ) := rfl

/-- Evaluation of tridegrees at polynomial weight 1 and exterior offset K. -/
def passiveVariables (K : ℕ) : Fin 3 → ChargeSeries :=
  ![MvPowerSeries.X 0, MvPowerSeries.X 0, MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ K]

theorem passiveVariables_hasSubst (K : ℕ) : MvPowerSeries.HasSubst (passiveVariables K) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [passiveVariables]

def passiveEvaluation (K : ℕ) : Series →ₐ[ℚ] ChargeSeries :=
  MvPowerSeries.substAlgHom (passiveVariables_hasSubst K)

theorem passiveEvaluation_X (K : ℕ) (i : Fin 3) :
    passiveEvaluation K (MvPowerSeries.X i) = passiveVariables K i := by
  exact MvPowerSeries.substAlgHom_X (passiveVariables_hasSubst K) i

private theorem passiveVariables_prod (K : ℕ) (e : Fin 3 →₀ ℕ) :
    e.prod (fun i a => passiveVariables K i ^ a) =
      MvPowerSeries.monomial
        (Finsupp.single 0 (e 0 + e 1 + K * e 2) + Finsupp.single 1 (e 2)) 1 := by
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (MvPowerSeries.X 0 : ChargeSeries) ^ e 0 *
    (MvPowerSeries.X 0 ^ e 1 * (MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ K) ^ e 2) = _
  rw [mul_pow, ← pow_mul]
  have he : (MvPowerSeries.X 0 : ChargeSeries) ^ e 0 *
      (MvPowerSeries.X 0 ^ e 1 * (MvPowerSeries.X 1 ^ e 2 * MvPowerSeries.X 0 ^ (K * e 2))) =
      MvPowerSeries.X 0 ^ (e 0 + e 1 + K * e 2) * MvPowerSeries.X 1 ^ e 2 := by
    simp only [pow_add]
    ring
  rw [he]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul]

theorem passiveEvaluation_monomial (K : ℕ) (e : Fin 3 →₀ ℕ) (q : ℚ) :
    passiveEvaluation K (MvPowerSeries.monomial e q) =
      MvPowerSeries.monomial
        (Finsupp.single 0 (e 0 + e 1 + K * e 2) + Finsupp.single 1 (e 2)) q := by
  rw [passiveEvaluation, MvPowerSeries.substAlgHom_monomial, passiveVariables_prod]
  change MvPowerSeries.C q * _ = _
  rw [← MvPowerSeries.monomial_zero_eq_C_apply,
    MvPowerSeries.monomial_mul_monomial, zero_add, mul_one]

private theorem boundedDegree_weight (K p A : ℕ) (m : BoundedMonomial p A) :
    boundedDegree 1 p A m 0 + boundedDegree 1 p A m 1 + K * boundedDegree 1 p A m 2 =
      enumeratorWeight K (boundedPassiveIndex p A m) := by
  simp [boundedDegree, enumeratorWeight, boundedPassiveIndex, Finset.sum_add_distrib,
    add_mul]
  ring

theorem passiveEvaluation_boundedMonomial (K p A : ℕ) (m : BoundedMonomial p A) :
    passiveEvaluation K (MvPowerSeries.monomial (boundedDegree 1 p A m) 1) =
      MvPowerSeries.monomial
        (Finsupp.single 0 (enumeratorWeight K (boundedPassiveIndex p A m)) + Finsupp.single 1 m.2.card) 1 := by
  rw [passiveEvaluation_monomial, boundedDegree_weight]
  simp [boundedDegree]

/-- Finite passive enumerator with all polynomial exponents bounded by A. -/
def passiveTruncated (K p A : ℕ) : ChargeSeries :=
  passiveEvaluation K (truncatedChainSeries 1 p A Finset.univ)

private theorem bidegree_eq_iff (w h : ℕ) (e : Fin 2 →₀ ℕ) :
    Finsupp.single 0 w + Finsupp.single 1 h = e ↔ w = e 0 ∧ h = e 1 := by
  constructor
  · intro he
    exact ⟨by simpa using congrArg (fun d => d 0) he,
      by simpa using congrArg (fun d => d 1) he⟩
  · rintro ⟨hw, hh⟩
    ext i
    fin_cases i <;> simp [hw, hh]

theorem coeff_passiveTruncated (K p A : ℕ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (passiveTruncated K p A) =
      (Nat.card {m : BoundedMonomial p A //
        enumeratorWeight K (boundedPassiveIndex p A m) = e 0 ∧ m.2.card = e 1} : ℚ) := by
  classical
  simp only [passiveTruncated, truncatedChainSeries, Finset.subset_univ, if_true,
    map_sum, passiveEvaluation_boundedMonomial, MvPowerSeries.coeff_monomial,
    Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro m hm
  have he := (eq_comm : e = Finsupp.single 0 (enumeratorWeight K (boundedPassiveIndex p A m)) +
      Finsupp.single 1 m.2.card ↔ _).trans
    (bidegree_eq_iff (enumeratorWeight K (boundedPassiveIndex p A m)) m.2.card e)
  simp only [he]

theorem coeff_passiveEnumerator_truncated (K p A : ℕ) (e : Fin 2 →₀ ℕ) (he : e 0 ≤ A) :
    MvPowerSeries.coeff e (passiveEnumerator K p) = MvPowerSeries.coeff e (passiveTruncated K p A) := by
  rw [coeff_passiveTruncated]
  change (Nat.card _ : ℚ) = _
  rw [Nat.card_congr (passiveFiberEquiv K p A (e 0) (e 1) he)]


theorem passiveEvaluation_even (K i : ℕ) :
    passiveEvaluation K (evenGeneratorSeries i) = (MvPowerSeries.X 0 : ChargeSeries) ^ (i + 1) := by
  rw [evenGeneratorSeries_eq, map_mul, map_pow, passiveEvaluation_X, passiveEvaluation_X]
  simp only [passiveVariables, Matrix.cons_val_zero, Matrix.cons_val_one, pow_succ]
  ring

theorem passiveEvaluation_odd (K i : ℕ) :
    passiveEvaluation K (oddGeneratorSeries 1 i) =
      (MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ (K + i + 1) := by
  rw [oddGeneratorSeries_eq, map_mul, map_mul, map_pow, map_pow,
    passiveEvaluation_X, passiveEvaluation_X, passiveEvaluation_X]
  simp [passiveVariables, pow_add, pow_one]
  ring

private theorem polynomial_denominator_eq (p : ℕ) :
    (∏ i : Fin p, (1 - (MvPowerSeries.X 0 : ChargeSeries) ^ (i.val + 1))) =
      qPochhammer (MvPowerSeries.X 0) (MvPowerSeries.X 0) p := by
  rw [Fin.prod_univ_eq_prod_range
    (fun i => 1 - (MvPowerSeries.X 0 : ChargeSeries) ^ (i + 1)) p]
  unfold qPochhammer
  apply Finset.prod_congr rfl
  intro i hi
  rw [pow_succ, mul_comm]

private theorem exterior_product_eq (K p : ℕ) :
    (∏ i : Fin p, (1 + (MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ (K + i.val + 1))) =
      qPochhammer (-MvPowerSeries.X 1 * (MvPowerSeries.X 0 : ChargeSeries) ^ (K + 1))
        (MvPowerSeries.X 0) p := by
  rw [Fin.prod_univ_eq_prod_range
    (fun i => 1 + (MvPowerSeries.X 1 : ChargeSeries) * MvPowerSeries.X 0 ^ (K + i + 1)) p]
  unfold qPochhammer
  apply Finset.prod_congr rfl
  intro i hi
  simp only [pow_add, pow_one]
  ring

/-- Clearing the denominator of the finite passive monomial enumerator. -/
theorem denominator_mul_passiveTruncated (K p A : ℕ) :
    qPochhammer (MvPowerSeries.X 0 : ChargeSeries) (MvPowerSeries.X 0) p * passiveTruncated K p A =
      (∏ i : Fin p, (1 - (MvPowerSeries.X 0 : ChargeSeries) ^ ((i.val + 1) * (A + 1)))) *
        qPochhammer (-MvPowerSeries.X 1 * (MvPowerSeries.X 0 : ChargeSeries) ^ (K + 1))
          (MvPowerSeries.X 0) p := by
  have he := congrArg (passiveEvaluation K) (denominator_mul_truncatedChainSeries 1 p A Finset.univ)
  simpa only [map_mul, map_prod, map_sub, map_add, map_one, map_pow,
    passiveEvaluation_even, passiveEvaluation_odd, ← pow_mul, polynomial_denominator_eq,
    exterior_product_eq, passiveTruncated] using he

private theorem coeff_weight_power_mul_zero (d : ℕ) (e : Fin 2 →₀ ℕ) (f : ChargeSeries)
    (he : e 0 < d) : MvPowerSeries.coeff e ((MvPowerSeries.X 0 : ChargeSeries) ^ d * f) = 0 := by
  classical
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul]
  have hn : ¬ Finsupp.single (0 : Fin 2) d ≤ e := by
    intro h
    have hh := h 0
    simp only [Finsupp.single_eq_same] at hh
    omega
  rw [if_neg hn]

private theorem coeff_passive_correction (p A : ℕ) (S : Finset (Fin p))
    (e : Fin 2 →₀ ℕ) (f : ChargeSeries) (he : e 0 ≤ A) :
    MvPowerSeries.coeff e ((∏ i ∈ S,
      (1 - (MvPowerSeries.X 0 : ChargeSeries) ^ ((i.val + 1) * (A + 1)))) * f) =
      MvPowerSeries.coeff e f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, mul_assoc, sub_mul, one_mul, map_sub,
      coeff_weight_power_mul_zero ((i.val + 1) * (A + 1)) e _ (by nlinarith), sub_zero, ih]

private theorem coeff_mul_congr_below_charge (e : Fin 2 →₀ ℕ) (f g k : ChargeSeries)
    (h : ∀ d ≤ e, MvPowerSeries.coeff d f = MvPowerSeries.coeff d g) :
    MvPowerSeries.coeff e (k * f) = MvPowerSeries.coeff e (k * g) := by
  classical
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he : p.1 + p.2 = e := Finset.mem_antidiagonal.mp hp
  rw [h p.2 (by rw [← he]; exact le_add_self)]

/-- The passive monomial Hilbert series, with its polynomial denominator cleared. -/
theorem passiveEnumerator_product (K p : ℕ) :
    qPochhammer (MvPowerSeries.X 0 : ChargeSeries) (MvPowerSeries.X 0) p * passiveEnumerator K p =
      qPochhammer (-MvPowerSeries.X 1 * (MvPowerSeries.X 0 : ChargeSeries) ^ (K + 1))
        (MvPowerSeries.X 0) p := by
  ext e
  rw [coeff_mul_congr_below_charge e (passiveEnumerator K p) (passiveTruncated K p (e 0)) _
    (fun d hd => coeff_passiveEnumerator_truncated K p (e 0) d (hd 0)),
    denominator_mul_passiveTruncated,
    coeff_passive_correction p (e 0) Finset.univ e _ le_rfl]

end TorusLinkHomology.HilbertSeries.GeneralReversal
