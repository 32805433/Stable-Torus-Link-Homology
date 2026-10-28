import TorusLinkHomology.Generation.UniversalTransferCycles
import TorusLinkHomology.Generation.SelectorCoefficient
import DGA.PowerSeriesAlgebra

/-! # The signed differential of the universal selector product -/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.UniversalTransfer

/-- Coefficientwise contraction has the signed Leibniz rule when every
coefficient of the left factor has exterior degree one. -/
theorem dSeries_odd_mul (N m : ℕ) (F G : PowerSeries A)
    (hF : ∀ i, F.coeff i ∈ LinearMap.range (ExteriorAlgebra.ι R)) :
    dSeries N m (F * G) = dSeries N m F * G - F * dSeries N m G := by
  ext n
  simp only [coeff_dSeries, PowerSeries.coeff_mul, map_sum, map_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  obtain ⟨w, hw⟩ := hF ij.1
  rw [← hw]
  change CliffordAlgebra.contractLeft (Q := 0) (functional N m)
    (ExteriorAlgebra.ι R w * G.coeff ij.2) =
    CliffordAlgebra.contractLeft (Q := 0) (functional N m) (ExteriorAlgebra.ι R w) *
      G.coeff ij.2 - ExteriorAlgebra.ι R w *
        CliffordAlgebra.contractLeft (Q := 0) (functional N m) (G.coeff ij.2)
  rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι, Algebra.smul_def]

/-- The signed deletion formula for a finite ordered family of odd series
whose differentials are scalar series. -/
theorem dSeries_ordered_product (N m q : ℕ) (F : Fin (q + 1) → PowerSeries A)
    (V : Fin (q + 1) → PowerSeries R)
    (hF : ∀ j i, (F j).coeff i ∈ LinearMap.range (ExteriorAlgebra.ι R))
    (hd : ∀ j, dSeries N m (F j) = scalarSeries (V j)) :
    dSeries N m (List.ofFn F).prod =
      ∑ j : Fin (q + 1), ((-1 : R) ^ j.val) •
        (scalarSeries (V j) * (List.ofFn (F ∘ j.succAbove)).prod) := by
  induction q with
  | zero =>
    simp [List.ofFn_succ, hd]
  | succ q ih =>
    conv_lhs => rw [List.ofFn_succ, List.prod_cons,
      dSeries_odd_mul N m _ _ (hF 0), hd 0,
      ih (fun j => F j.succ) (fun j => V j.succ)
        (fun j i => hF j.succ i) (fun j => hd j.succ)]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [List.ofFn_succ, List.prod_cons]
    have htail : (fun i : Fin q => (F ∘ j.succ.succAbove) i.succ) =
        (F ∘ Fin.succ) ∘ j.succAbove := by
      funext i
      simp only [Function.comp_apply, Fin.succ_succAbove_succ]
    change -(F 0 * (((-1 : R) ^ j.val) •
      (scalarSeries (V j.succ) * (List.ofFn ((F ∘ Fin.succ) ∘ j.succAbove)).prod))) = _
    have hcomm : F 0 * scalarSeries (V j.succ) = scalarSeries (V j.succ) * F 0 :=
      (PowerSeries.scalarSeries_commutes (V j.succ) (F 0)).symm
    rw [mul_smul_comm, ← mul_assoc, hcomm, mul_assoc]
    rw [htail]
    simp only [Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
      Function.comp_apply, Fin.succ_succAbove_zero]

/-- The ordered product whose differential is the Euler deletion expression. -/
def selectorBoundarySeries (q : ℕ) (p : Polynomial ℚ) (b : ℤ)
    (C : PowerSeries A) : PowerSeries A :=
  (List.ofFn (fun i : Fin (q + 1) =>
    (CoefficientSeries.shiftedEuler b)^[i.val]
      (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b C))).prod

/-- An Euler derivative of a rational-selector output. -/
def selectorJet {B : Type*} [Ring B] [Algebra R B] (p : Polynomial ℚ)
    (b : ℤ) (a : ℕ) (F : PowerSeries B) : PowerSeries B :=
  (CoefficientSeries.shiftedEuler b)^[a]
    (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b F)

theorem coeff_selectorJet {B : Type*} [Ring B] [Algebra R B] (p : Polynomial ℚ)
    (b : ℤ) (a i : ℕ) (F : PowerSeries B) :
    (selectorJet p b a F).coeff i =
      algebraMap ℚ R (CoefficientSelector.eulerWeight p b a i) • F.coeff i :=
  CoefficientSelector.coeff_iterate_evalEuler_map p b a i F

theorem selectorJet_sub {B : Type*} [Ring B] [Algebra R B] (p : Polynomial ℚ)
    (b : ℤ) (a : ℕ) (F G : PowerSeries B) :
    selectorJet p b a (F - G) = selectorJet p b a F - selectorJet p b a G := by
  ext i
  simp only [coeff_selectorJet, map_sub, smul_sub]

theorem selectorJet_scalarSeries (p : Polynomial ℚ) (b : ℤ) (a : ℕ)
    (F : PowerSeries R) :
    scalarSeries (selectorJet p b a F) = selectorJet p b a (scalarSeries F) := by
  ext i
  simp only [scalarSeries, PowerSeries.coeff_map, coeff_selectorJet, smul_eq_mul,
    Algebra.smul_def, map_mul]

theorem dSeries_selectorJet (N m : ℕ) (p : Polynomial ℚ) (b : ℤ) (a : ℕ)
    (F : PowerSeries A) :
    dSeries N m (selectorJet p b a F) = selectorJet p b a (dSeries N m F) := by
  ext i
  simp only [coeff_dSeries, coeff_selectorJet, map_smul]

/-- Aligning deficits lowers the Euler upper exponent by exactly m. -/
theorem selectorJet_X_pow_mul {B : Type*} [Ring B] [Algebra R B]
    (p : Polynomial ℚ) (b : ℤ) (a m : ℕ) (F : PowerSeries B) :
    selectorJet p b a (PowerSeries.X ^ m * F) =
      PowerSeries.X ^ m * selectorJet p (b - m) a F := by
  ext i
  simp only [coeff_selectorJet, PowerSeries.coeff_X_pow_mul']
  split_ifs with hi
  · have he : CoefficientSelector.eulerWeight p b a i =
        CoefficientSelector.eulerWeight p (b - m) a (i - m) := by
      have hc : ((b - (m : ℤ) : ℤ) : ℚ) - ((i - m : ℕ) : ℚ) = (b : ℚ) - (i : ℚ) := by
        rw [Int.cast_sub, Int.cast_natCast, Nat.cast_sub hi]
        ring
      simp only [CoefficientSelector.eulerWeight, hc]
    rw [he]
  · simp

theorem selectorJet_cSeries_coeff_mem_range (p : Polynomial ℚ) (b : ℤ) (a i : ℕ) :
    (selectorJet p b a cSeries).coeff i ∈ LinearMap.range (ExteriorAlgebra.ι R) := by
  rw [coeff_selectorJet]
  refine ⟨algebraMap ℚ R (CoefficientSelector.eulerWeight p b a i) •
    Finsupp.single (Sum.inl i) 1, ?_⟩
  rw [cSeries, PowerSeries.coeff_mk]
  change (ExteriorAlgebra.ι R : V →ₗ[R] A)
    (algebraMap ℚ R (CoefficientSelector.eulerWeight p b a i) • Finsupp.single (Sum.inl i) 1) =
      algebraMap ℚ R (CoefficientSelector.eulerWeight p b a i) •
        (ExteriorAlgebra.ι R : V →ₗ[R] A) (Finsupp.single (Sum.inl i) 1)
  exact (ExteriorAlgebra.ι R : V →ₗ[R] A).map_smul _ _

/-- First form of the selector differential: the signed deletion expression
with the full scalar differential dC. -/
theorem d_selectorBoundarySeries_raw (N m q : ℕ) (p : Polynomial ℚ) (b : ℤ) :
    dSeries N m (selectorBoundarySeries q p b cSeries) =
      CoefficientSelector.eulerDeletionSeries q p b b
        (scalarSeries (PowerSeries.mk (shiftedV m) - ySeries ^ N)) cSeries := by
  have hd (j : Fin (q + 1)) :
      dSeries N m (selectorJet p b j.val cSeries) =
        scalarSeries (selectorJet p b j.val (PowerSeries.mk (shiftedV m) - ySeries ^ N)) := by
    rw [dSeries_selectorJet, selectorJet_scalarSeries, dSeries_cSeries]
    rfl
  have hp := dSeries_ordered_product N m q
    (fun j => selectorJet p b j.val cSeries)
    (fun j => selectorJet p b j.val (PowerSeries.mk (shiftedV m) - ySeries ^ N))
    (fun j i => selectorJet_cSeries_coeff_mem_range p b j.val i) hd
  simp_rw [selectorJet_scalarSeries] at hp
  exact hp

theorem eulerDeletionSeries_sub_left (q : ℕ) (p : Polynomial ℚ) (b ell : ℤ)
    (F G C : PowerSeries A) :
    CoefficientSelector.eulerDeletionSeries q p b ell (F - G) C =
      CoefficientSelector.eulerDeletionSeries q p b ell F C -
        CoefficientSelector.eulerDeletionSeries q p b ell G C := by
  change (∑ j : Fin (q + 1), ((-1 : R) ^ j.val) •
    (selectorJet p ell j.val (F - G) * _)) = _
  simp only [selectorJet_sub, sub_mul, smul_sub, Finset.sum_sub_distrib]
  rfl

theorem eulerDeletionSeries_X_pow_mul_left (q : ℕ) (p : Polynomial ℚ) (b ell : ℤ)
    (m : ℕ) (F C : PowerSeries A) :
    CoefficientSelector.eulerDeletionSeries q p b ell (PowerSeries.X ^ m * F) C =
      PowerSeries.X ^ m * CoefficientSelector.eulerDeletionSeries q p b (ell - m) F C := by
  unfold CoefficientSelector.eulerDeletionSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((-1 : R) ^ j.val) • (selectorJet p ell j.val (PowerSeries.X ^ m * F) * _) =
    PowerSeries.X ^ m * (((-1 : R) ^ j.val) • (selectorJet p (ell - m) j.val F * _))
  rw [selectorJet_X_pow_mul, mul_assoc, mul_smul_comm]

/-- ET-11: the selector boundary has exactly the shifted V deletion term
minus the U^N deletion term. This holds before any coefficient extraction. -/
theorem d_selectorBoundarySeries (N m q : ℕ) (p : Polynomial ℚ) (b : ℤ) :
    dSeries N m (selectorBoundarySeries q p b cSeries) =
      PowerSeries.X ^ m *
        CoefficientSelector.eulerDeletionSeries q p b (b - m) (scalarSeries vSeries) cSeries -
      CoefficientSelector.eulerDeletionSeries q p b b (scalarSeries (ySeries ^ N)) cSeries := by
  rw [d_selectorBoundarySeries_raw, mk_shiftedV_eq, map_sub, map_mul]
  have hX : scalarSeries (PowerSeries.X ^ m) = PowerSeries.X ^ m := by
    simp [scalarSeries]
  rw [hX, eulerDeletionSeries_sub_left, eulerDeletionSeries_X_pow_mul_left]

/-- Extracting at the shifted deficit gives a literal boundary relation
between the V deletion coefficient and the U^N deletion coefficient. -/
theorem d_selectorBoundarySeries_coeff (N m q : ℕ) (p : Polynomial ℚ) (b : ℤ) (i : ℕ) :
    d N m ((selectorBoundarySeries q p b cSeries).coeff (m + i)) =
      (CoefficientSelector.eulerDeletionSeries q p b (b - m)
        (scalarSeries vSeries) cSeries).coeff i -
      (CoefficientSelector.eulerDeletionSeries q p b b
        (scalarSeries (ySeries ^ N)) cSeries).coeff (m + i) := by
  have h := congrArg (fun F : PowerSeries A => F.coeff (m + i))
    (d_selectorBoundarySeries N m q p b)
  simpa only [coeff_dSeries, map_sub, PowerSeries.coeff_X_pow_mul',
    Nat.le_add_right, if_true, Nat.add_sub_cancel_left] using h

end TorusLinkHomology.UniversalTransfer
