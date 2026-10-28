import TorusLinkHomology.Generation.UniversalTransferUniqueness
import TorusLinkHomology.Generation.SelectorCoefficient
import TorusLinkHomology.Generation.UniversalTransferCycles

/-!
# No-v closure and selector coefficients in the universal transfer

The finite polynomial construction of beta proves coefficient independence
without division by y₀. Closure under the operations defining P, evaluation
at Q=0, and the selected deletion coefficient supply the residue comparison.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.UniversalTransfer

@[simp] theorem pderiv_rename_inl (h : ℕ) (p : MvPolynomial ℕ ℚ) :
    MvPolynomial.pderiv (Sum.inr h) (MvPolynomial.rename Sum.inl p : R) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [Derivation.leibniz, hp]

/-- A polynomial in the y-family, embedded in the exterior algebra, has no v. -/
theorem noV_rename_inl (p : MvPolynomial ℕ ℚ) :
    NoV (algebraMap R A (MvPolynomial.rename Sum.inl p)) :=
  noV_algebraMap (fun h => pderiv_rename_inl h p)

/-- beta is the image of a polynomial in the y-variables alone. -/
theorem beta_eq_rename_inl (N t : ℕ) :
    beta N t = MvPolynomial.rename Sum.inl
      (CoefficientSeries.leadingQuotient N
        (PowerSeries.mk (MvPolynomial.X : ℕ → MvPolynomial ℕ ℚ)) t) := by
  have hy : PowerSeries.map (MvPolynomial.rename (R := ℚ) (Sum.inl : ℕ → ℕ ⊕ ℕ)).toRingHom
      (PowerSeries.mk (MvPolynomial.X : ℕ → MvPolynomial ℕ ℚ)) = ySeries := by
    ext i
    simp [ySeries, y]
  symm
  change (MvPolynomial.rename (R := ℚ) (Sum.inl : ℕ → ℕ ⊕ ℕ)).toRingHom _ = _
  rw [CoefficientSeries.map_leadingQuotient, hy]
  rfl

@[simp] theorem pderiv_beta (h N t : ℕ) :
    MvPolynomial.pderiv (Sum.inr h) (beta N t) = 0 := by
  rw [beta_eq_rename_inl, pderiv_rename_inl]

@[simp] theorem noV_beta (N t : ℕ) : NoV (algebraMap R A (beta N t)) :=
  noV_algebraMap (fun h => pderiv_beta h N t)

@[simp] theorem noV_etaPrime (N m : ℕ) : NoV (etaPrime N m) := by
  apply (noV_oddQ 0).smul
  intro h
  exact MvPolynomial.pderiv_C

@[simp] theorem noV_orderedA (q : ℕ) (t : Fin q → ℕ) : NoV (orderedA q t) := by
  induction q with
  | zero => simp [orderedA, ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    rw [orderedA, ExteriorAlgebra.ιMulti_succ_apply]
    exact (noV_oddA (t 0)).mul (ih (fun i => t i.succ))

@[simp] theorem noV_betaDeletion (N q : ℕ) (t : Fin (q + 1) → ℕ) :
    NoV (betaDeletion N q t) := by
  unfold betaDeletion
  apply noVSubalgebra.sum_mem
  intro i _
  apply (noV_orderedA q (t ∘ i.succAbove)).smul
  intro h
  simp [Derivation.leibniz, Derivation.leibniz_pow]

@[simp] theorem noV_etaPrime_mul_betaDeletion (N m q : ℕ) (t : Fin (q + 1) → ℕ) :
    NoV (etaPrime N m * betaDeletion N q t) :=
  (noV_etaPrime N m).mul (noV_betaDeletion N q t)

@[simp] theorem eraseQ_orderedA (q : ℕ) (t : Fin q → ℕ) :
    eraseQ (orderedA q t) = orderedA q t := by
  induction q with
  | zero => simp [orderedA, ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    rw [orderedA, ExteriorAlgebra.ιMulti_succ_apply, map_mul]
    change eraseQ (oddA (t 0)) * eraseQ (orderedA q (fun i => t i.succ)) =
      oddA (t 0) * orderedA q (fun i => t i.succ)
    rw [eraseQ_oddA, ih]

@[simp] theorem eraseQ_etaPrime (N m : ℕ) : eraseQ (etaPrime N m) = 0 := by
  simp [etaPrime]

@[simp] theorem eraseQ_betaDeletion (N q : ℕ) (t : Fin (q + 1) → ℕ) :
    eraseQ (betaDeletion N q t) = betaDeletion N q t := by
  simp [betaDeletion]

@[simp] theorem eraseQ_omega (N m q : ℕ) (t : Fin (q + 1) → ℕ) :
    eraseQ (omega N m q t) = v 0 • orderedA (q + 1) t := by
  simp [omega]

/-- Every coefficient of a formal series is independent of v. -/
def NoVSeries (F : PowerSeries A) : Prop := ∀ i, NoV (F.coeff i)

theorem NoV.nsmul {x : A} (hx : NoV x) (n : ℕ) : NoV (n • x) := by
  intro h
  rw [map_nsmul, hx h, smul_zero]

theorem NoV.zsmul {x : A} (hx : NoV x) (n : ℤ) : NoV (n • x) := by
  intro h
  rw [map_zsmul, hx h, smul_zero]

@[simp] theorem noVSeries_zero : NoVSeries 0 := by
  intro i
  simp

@[simp] theorem noVSeries_one : NoVSeries 1 := by
  intro i
  by_cases hi : i = 0 <;> simp [PowerSeries.coeff_one, hi]

@[simp] theorem noVSeries_X : NoVSeries PowerSeries.X := by
  intro i
  by_cases hi : i = 1 <;> simp [PowerSeries.coeff_X, hi]

theorem NoVSeries.add {F G : PowerSeries A} (hF : NoVSeries F) (hG : NoVSeries G) :
    NoVSeries (F + G) := by
  intro i
  simpa only [map_add] using (hF i).add (hG i)

theorem NoVSeries.sub {F G : PowerSeries A} (hF : NoVSeries F) (hG : NoVSeries G) :
    NoVSeries (F - G) := by
  intro i
  simpa only [map_sub] using (hF i).sub (hG i)

theorem NoVSeries.nsmul {F : PowerSeries A} (hF : NoVSeries F) (n : ℕ) :
    NoVSeries (n • F) := by
  intro i
  simpa only [map_nsmul] using (hF i).nsmul n

theorem NoVSeries.mul {F G : PowerSeries A} (hF : NoVSeries F) (hG : NoVSeries G) :
    NoVSeries (F * G) := by
  intro i
  rw [PowerSeries.coeff_mul]
  apply noVSubalgebra.sum_mem
  intro ij _
  exact (hF ij.1).mul (hG ij.2)

theorem NoVSeries.pow {F : PowerSeries A} (hF : NoVSeries F) (n : ℕ) :
    NoVSeries (F ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [pow_succ] using ih.mul hF

theorem NoVSeries.shiftedEuler {F : PowerSeries A} (hF : NoVSeries F) (b : ℤ) :
    NoVSeries (CoefficientSeries.shiftedEuler b F) := by
  intro i
  rw [CoefficientSeries.coeff_shiftedEuler]
  exact (hF i).zsmul _

@[simp] theorem noVSeries_cSeries : NoVSeries cSeries := by
  intro i
  simp [cSeries]

@[simp] theorem noVSeries_qSeries : NoVSeries qSeries := by
  intro i
  simp [qSeries]

@[simp] theorem noVSeries_scalar_ySeries : NoVSeries (scalarSeries ySeries) := by
  intro i
  simp [scalarSeries, ySeries]

theorem NoVSeries.expression {U F : PowerSeries A} (hU : NoVSeries U) (hF : NoVSeries F)
    (N : ℕ) (r b : ℤ) : NoVSeries (CoefficientSeries.expression N r b U F) :=
  (hU.mul (hF.shiftedEuler b)).sub (((hU.shiftedEuler r).mul hF).nsmul N)

@[simp] theorem noVSeries_pSeries (N m r : ℕ) : NoVSeries (pSeries N m r) := by
  exact ((noVSeries_X.pow m).mul noVSeries_qSeries).nsmul N |>.sub
    (noVSeries_scalar_ySeries.expression noVSeries_cSeries N r (N * r))

/-- The selected Euler deletion coefficient, in the universal named series. -/
theorem selector_deletion_coeff {q : ℕ} (b : ℤ) (m k : ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q = T.card) :
    (CoefficientSelector.eulerDeletionSeries q (CoefficientSelector.selector b k T) b (b - m)
      (scalarSeries vSeries) cSeries).coeff (∑ t ∈ T, t) =
      (v 0 * algebraMap ℚ R (CoefficientSelector.transferScalar m k T)) •
        orderedA q (T.orderEmbOfFin hq.symm) := by
  have hV : scalarSeries vSeries = CoefficientSelector.scalarSeries (M := V) v := by
    ext i
    simp [scalarSeries, vSeries, CoefficientSelector.scalarSeries]
  have hC : cSeries = CoefficientSelector.weightedOddSeries
      (fun _ => (1 : R)) (fun i => Finsupp.single (Sum.inl i) 1) := by
    ext i
    simp [cSeries, oddA, CoefficientSelector.weightedOddSeries]
  rw [hV, hC]
  exact CoefficientSelector.eulerDeletionSeries_selector_coeff b m k T hT hq v
    (fun i => Finsupp.single (Sum.inl i) 1)

end TorusLinkHomology.UniversalTransfer
