import TorusLinkHomology.HilbertSeries.ReversalDimensions
import TorusLinkHomology.HilbertSeries.PassiveEnumerator
import TorusLinkHomology.HilbertSeries.AuxiliaryNumerator

/-! Generating-series assembly for the general reversal decomposition. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- The descending weights of the active polynomial variables complement the
ascending weights of the passive polynomial variables. -/
theorem auxiliaryDenominator_split (m p : ℕ) :
    auxiliaryDenominator (m + p) =
      qPochhammer (MvPowerSeries.X 0 : ChargeSeries) (MvPowerSeries.X 0) p *
        ∏ j ∈ Finset.range m, (1 - (MvPowerSeries.X 0 : ChargeSeries) ^ (m + p - j)) := by
  rw [auxiliaryDenominator, show m + p = p + m by omega, qPochhammer_add]
  congr 1
  rw [← Finset.prod_range_reflect
    (fun j => 1 - (MvPowerSeries.X 0 : ChargeSeries) ^ (p + m - j)) m]
  unfold qPochhammer
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have he : p + m - (m - 1 - j) = p + 1 + j := by omega
  rw [he]
  congr 1
  rw [← pow_succ', ← pow_add]

/-- Clearing denominators in a reversal product identity. -/
theorem cleared_reversal_of_series_product (N m p C : ℕ) (hN : 0 < N)
    (hm : m - 1 ≤ C) (hr : C < m + p)
    (hseries : Auxiliary.hilbertSeries N (m + p) (N * (m + p) - m) =
      GeneralReversal.passiveEnumerator (N * (m + p)) p *
        positiveSpecialization C (m + p) (hilbertSeries N m)) :
    auxiliaryDenominator (m + p) *
      Auxiliary.hilbertSeries N (m + p) (N * (m + p) - m) =
      passiveExteriorProduct N (m + p) m *
        specializedHilbertNumerator N m C (m + p) := by
  rw [hseries, auxiliaryDenominator_split, specializedHilbertNumerator,
    positiveSpecialization_mul C (m + p) _ _ hr
      (coneSupported_denominator C m hm) (coneSupported_hilbertSeries N m C hN hm),
    positiveSpecialization_denominator C (m + p) m hr hm]
  have hp := GeneralReversal.passiveEnumerator_product (N * (m + p)) p
  simp only [passiveExteriorProduct, Nat.add_sub_cancel_left]
  linear_combination
    (∏ j ∈ Finset.range m, (1 - (MvPowerSeries.X 0 : ChargeSeries) ^ (m + p - j))) *
      positiveSpecialization C (m + p) (hilbertSeries N m) * hp

namespace GeneralReversal

/-- A convolution index records the passive and active bidegrees, a passive
monomial, and one original tridegree in the positive-specialization fiber. -/
def ReversalProductIndex (C r K p w h : ℕ) :=
  Σ d : {d : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) //
      d ∈ Finset.antidiagonal (Finsupp.single 0 w + Finsupp.single 1 h)},
    {t : ChainIndex p // enumeratorWeight K t = d.val.1 0 ∧ t.2.card = d.val.1 1} ×
      {ab : ℕ × ℕ // ab ∈ specializationFiber C r (d.val.2 0)}

instance reversalProductIndex_fintype (C r K p w h : ℕ) :
    Fintype (ReversalProductIndex C r K p w h) := by
  classical
  unfold ReversalProductIndex
  letI (d : {d : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) //
      d ∈ Finset.antidiagonal (Finsupp.single 0 w + Finsupp.single 1 h)}) :
      Fintype {t : ChainIndex p // enumeratorWeight K t = d.val.1 0 ∧ t.2.card = d.val.1 1} :=
    Fintype.ofFinite _
  infer_instance

/-- Coefficients of the reversal product as one finite convolution sum. -/
theorem coeff_reversal_product (N m C r K p w h : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 w + Finsupp.single 1 h)
      (passiveEnumerator K p * positiveSpecialization C r (hilbertSeries N m)) =
    ∑ i : ReversalProductIndex C r K p w h,
      (homologyDimension N m i.2.2.val.1 i.2.2.val.2 (i.1.val.2 1) : ℚ) := by
  classical
  let (d : {d : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) //
      d ∈ Finset.antidiagonal (Finsupp.single 0 w + Finsupp.single 1 h)}) :
      Fintype {t : ChainIndex p // enumeratorWeight K t = d.val.1 0 ∧ t.2.card = d.val.1 1} :=
    Fintype.ofFinite _
  rw [MvPowerSeries.coeff_mul]
  change _ = ∑ i : Sigma _, _
  rw [Fintype.sum_sigma]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Fintype.sum_prod_type]
  have he : d.val.2 = Finsupp.single 0 (d.val.2 0) + Finsupp.single 1 (d.val.2 1) := by
    ext j
    fin_cases j <;> simp
  rw [coeff_passiveEnumerator]
  change _ * positiveSpecialization C r (hilbertSeries N m) d.val.2 = _
  have hf := positiveSpecialization_coeff_fiber C r (d.val.2 0) (d.val.2 1) (hilbertSeries N m)
  rw [← he] at hf
  rw [hf]
  simp only [hilbertSeries, MvPowerSeries.coeff_apply, tridegree_apply_zero,
    tridegree_apply_one, tridegree_apply_two]
  rw [Nat.card_eq_fintype_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  exact (Finset.sum_attach _ _).symm

/-- Convolution index attached to a finite homogeneous reversal summand. -/
def ReversalFiber.productIndex {N m p C w h : ℕ} (hr : C < m + p)
    (i : ReversalFiber N m p C w h) : ReversalProductIndex C (m + p) (N * (m + p)) p w h := by
  classical
  let t := i.passiveIndex
  have hb : i.b.val ≤ (m + p) * i.a.val :=
    i.support_bound.trans (Nat.mul_le_mul_right _ hr.le)
  refine ⟨⟨(Finsupp.single 0 (enumeratorWeight (N * (m + p)) t) + Finsupp.single 1 t.2.card,
      Finsupp.single 0 ((m + p) * i.a.val - i.b.val) + Finsupp.single 1 i.k.val), ?_⟩,
    ⟨⟨t, ?_⟩, ⟨(i.a.val, i.b.val), ?_⟩⟩⟩
  · apply Finset.mem_antidiagonal.mpr
    have hw := i.weight_eq
    have hh := i.degree_eq
    change enumeratorWeight (N * (m + p)) t + (m + p) * i.a.val = w + i.b.val at hw
    change i.k.val + t.2.card = h at hh
    ext j
    fin_cases j <;> simp only [Finsupp.add_apply, Finsupp.single_apply] <;> norm_num
    · omega
    · omega
  · simp
  · apply (mem_specializationFiber hr).mpr
    exact ⟨i.support_bound, by simp⟩

private theorem reversalProductIndex_ext {N m p C w h : ℕ} (hr : C < m + p)
    (i j : ReversalProductIndex C (m + p) (N * (m + p)) p w h)
    (hp : i.2.1.val = j.2.1.val) (ha : i.2.2.val.1 = j.2.2.val.1)
    (hb : i.2.2.val.2 = j.2.2.val.2) (hk : i.1.val.2 1 = j.1.val.2 1) : i = j := by
  have hd : i.1 = j.1 := by
    apply Subtype.ext
    apply Prod.ext
    · ext t
      fin_cases t
      · exact i.2.1.property.1.symm.trans ((congrArg (enumeratorWeight (N * (m + p))) hp).trans
          j.2.1.property.1)
      · exact i.2.1.property.2.symm.trans ((congrArg (fun t : ChainIndex p => t.2.card) hp).trans
          j.2.1.property.2)
    · have hi := (mem_specializationFiber hr).mp i.2.2.property
      have hj := (mem_specializationFiber hr).mp j.2.2.property
      ext t
      fin_cases t
      · change i.1.val.2 0 = j.1.val.2 0
        rw [← hi.2, ← hj.2, ha, hb]
      · exact hk
  cases i with
  | mk di xi =>
    cases j with
    | mk dj xj =>
      dsimp only at hd
      subst dj
      congr 1
      apply Prod.ext
      · exact Subtype.ext hp
      · exact Subtype.ext (Prod.ext ha hb)

/-- The finite homogeneous index and the coefficient-convolution index coincide. -/
def reversalIndexEquiv (N m p C w h : ℕ) (hr : C < m + p) :
    ReversalFiber N m p C w h ≃ ReversalProductIndex C (m + p) (N * (m + p)) p w h :=
  Equiv.ofBijective (ReversalFiber.productIndex hr) (by
    constructor
    · intro i j he
      apply ReversalFiber.eq_of_passiveIndex_degree_eq
      · exact congrArg (fun i => i.2.1.val) he
      · apply Prod.ext
        · exact congrArg (fun i => i.2.2.val.1) he
        · apply Prod.ext
          · exact congrArg (fun i => i.2.2.val.2) he
          · simpa [ReversalFiber.productIndex, ReversalFiber.degree] using
              congrArg (fun i => i.1.val.2 1) he
    · intro j
      have hs := Finset.mem_antidiagonal.mp j.1.property
      have hw : j.1.val.1 0 + j.1.val.2 0 = w := by
        simpa using congrArg (fun e => e 0) hs
      have hh : j.1.val.1 1 + j.1.val.2 1 = h := by
        simpa using congrArg (fun e => e 1) hs
      have hf : j.2.2.val.2 ≤ C * j.2.2.val.1 ∧
          (m + p) * j.2.2.val.1 - j.2.2.val.2 = j.1.val.2 0 :=
        (mem_specializationFiber hr).mp j.2.2.property
      have hb : j.2.2.val.2 ≤ (m + p) * j.2.2.val.1 :=
        hf.1.trans (Nat.mul_le_mul_right _ hr.le)
      have ha : j.2.2.val.1 ≤ w := by
        have hm := Nat.mul_le_mul_right j.2.2.val.1 (show C + 1 ≤ m + p by omega)
        rw [Nat.add_mul, one_mul] at hm
        omega
      let t := j.2.1.val
      have ht : enumeratorWeight (N * (m + p)) t ≤ w := by
        change enumeratorWeight (N * (m + p)) j.2.1.val ≤ w
        rw [j.2.1.property.1]
        omega
      let bt : BoundedMonomial p w :=
        (fun q => ⟨t.1 q, Nat.lt_succ_of_le
          ((exponent_le_enumeratorWeight (N * (m + p)) p t q).trans ht)⟩, t.2)
      have hbt : fiberPassiveIndex bt = t := by
        apply Prod.ext
        · ext q
          simp [fiberPassiveIndex, bt]
        · rfl
      let i : ReversalFiber N m p C w h :=
        { passive := bt
          a := ⟨j.2.2.val.1, by omega⟩
          b := ⟨j.2.2.val.2, by have := Nat.mul_le_mul_left C ha; omega⟩
          k := ⟨j.1.val.2 1, by omega⟩
          weight_eq := by
            change passiveWeight N m p (fiberPassiveIndex bt) + (m + p) * j.2.2.val.1 = w + j.2.2.val.2
            rw [hbt]
            change enumeratorWeight (N * (m + p)) t + _ = _
            change enumeratorWeight (N * (m + p)) j.2.1.val + _ = _
            rw [j.2.1.property.1]
            omega
          degree_eq := by
            change j.1.val.2 1 + t.2.card = h
            change j.1.val.2 1 + j.2.1.val.2.card = h
            rw [j.2.1.property.2]
            omega
          support_bound := hf.1 }
      refine ⟨i, reversalProductIndex_ext hr _ j ?_ rfl rfl ?_⟩
      · exact hbt
      · simp [ReversalFiber.productIndex, i])

set_option maxHeartbeats 1200000 in
/-- Product coefficients are precisely the finite homogeneous summand ranks. -/
theorem coeff_reversal_product_fiber (N m p C w h : ℕ) (hr : C < m + p) :
    MvPowerSeries.coeff (Finsupp.single 0 w + Finsupp.single 1 h)
      (passiveEnumerator (N * (m + p)) p *
        positiveSpecialization C (m + p) (hilbertSeries N m)) =
      (∑ i : ReversalFiber N m p C w h,
        homologyDimension N m i.a.val i.b.val i.k.val : ℕ) := by
  rw [coeff_reversal_product, Nat.cast_sum]
  symm
  apply Fintype.sum_equiv (reversalIndexEquiv N m p C w h hr)
  intro i
  simp only [reversalIndexEquiv, Equiv.ofBijective, Equiv.coe_fn_mk]
  simp [ReversalFiber.productIndex]


/-- The homogeneous rank convolution implies the reversal Hilbert product. -/
theorem reversal_series_of_dimensions (N m p C : ℕ) (hr : C < m + p)
    (hdim : ∀ w h, Auxiliary.homologyDimension N (N * (m + p) - m) (m + p) w h =
      ∑ i : ReversalFiber N m p C w h, homologyDimension N m i.a.val i.b.val i.k.val) :
    Auxiliary.hilbertSeries N (m + p) (N * (m + p) - m) =
      passiveEnumerator (N * (m + p)) p *
        positiveSpecialization C (m + p) (hilbertSeries N m) := by
  ext e
  have he : e = Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) := by
    ext j
    fin_cases j <;> simp
  have hp := coeff_reversal_product_fiber N m p C (e 0) (e 1) hr
  rw [← he] at hp
  rw [hp]
  change (Auxiliary.homologyDimension N (N * (m + p) - m) (m + p) (e 0) (e 1) : ℚ) = _
  rw [hdim]

/-- Homogeneous rank convolution, passive enumeration, and denominator clearing
assemble to the precise premise used in the finite-formula proof. -/
theorem cleared_reversal_of_dimensions (N r m C : ℕ) (hN : 0 < N)
    (hmr : m ≤ r) (hm : m - 1 ≤ C) (hr : C < r)
    (hdim : ∀ w h, Auxiliary.homologyDimension N (N * (m + (r - m)) - m)
        (m + (r - m)) w h =
      ∑ i : ReversalFiber N m (r - m) C w h,
        homologyDimension N m i.a.val i.b.val i.k.val) :
    auxiliaryDenominator r * Auxiliary.hilbertSeries N r (N * r - m) =
      passiveExteriorProduct N r m * specializedHilbertNumerator N m C r := by
  have he : m + (r - m) = r := Nat.add_sub_of_le hmr
  have hh := cleared_reversal_of_series_product N m (r - m) C hN hm (by omega)
    (reversal_series_of_dimensions N m (r - m) C (by omega) hdim)
  simpa only [he] using hh

/-- General graded reversal with all passive factors cleared. -/
theorem cleared_reversal (N r m C : ℕ) (hN : 0 < N)
    (hmr : m ≤ r) (hm : m - 1 ≤ C) (hr : C < r) :
    auxiliaryDenominator r * Auxiliary.hilbertSeries N r (N * r - m) =
      passiveExteriorProduct N r m * specializedHilbertNumerator N m C r := by
  apply cleared_reversal_of_dimensions N r m C hN hmr hm hr
  intro w h
  exact homologyDimension_reversal N m (r - m) C w h hN hm (by omega)

end GeneralReversal
end TorusLinkHomology.HilbertSeries
