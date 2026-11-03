import TorusLinkHomology.Generation.SelectorCoefficient
import DGA.PowerSeriesAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# The ordered selector product and its differential

For a series of degree-one generators with a scalar differential, the differential
of the ordered product of its selector jets is the Euler deletion expression. Its
selected coefficient splits into the part using only deficits below `m` and one
Vandermonde term, which has the generator at deficit `m` as its first factor.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientSelector

variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Module R M]

/-- The ordered product whose differential is the Euler deletion expression. -/
def selectorBoundarySeries (q : ℕ) (p : Polynomial ℚ) (b : ℤ)
    (C : PowerSeries (ExteriorAlgebra R M)) : PowerSeries (ExteriorAlgebra R M) :=
  (List.ofFn (fun a : Fin (q + 1) =>
    (CoefficientSeries.shiftedEuler b)^[a.val]
      (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b C))).prod

/-- Contraction with a functional, applied to each coefficient of a series. -/
def contractSeries (f : Module.Dual R M) (G : PowerSeries (ExteriorAlgebra R M)) :
    PowerSeries (ExteriorAlgebra R M) :=
  PowerSeries.mk fun i => CliffordAlgebra.contractLeft (Q := 0) f (G.coeff i)

omit [Algebra ℚ R] in
@[simp] theorem coeff_contractSeries (f : Module.Dual R M)
    (G : PowerSeries (ExteriorAlgebra R M)) (i : ℕ) :
    (contractSeries f G).coeff i = CliffordAlgebra.contractLeft (Q := 0) f (G.coeff i) :=
  PowerSeries.coeff_mk _ _

omit [Algebra ℚ R] in
/-- Contraction has the signed Leibniz rule when every coefficient of the left
factor has exterior degree one. -/
theorem contractSeries_odd_mul (f : Module.Dual R M)
    (G H : PowerSeries (ExteriorAlgebra R M))
    (hG : ∀ i, G.coeff i ∈ LinearMap.range (ExteriorAlgebra.ι R (M := M))) :
    contractSeries f (G * H) = contractSeries f G * H - G * contractSeries f H := by
  ext n
  simp only [coeff_contractSeries, PowerSeries.coeff_mul, map_sum, map_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  obtain ⟨w, hw⟩ := hG ij.1
  rw [← hw]
  change CliffordAlgebra.contractLeft (Q := 0) f
    (ExteriorAlgebra.ι R w * H.coeff ij.2) =
    CliffordAlgebra.contractLeft (Q := 0) f (ExteriorAlgebra.ι R w) *
      H.coeff ij.2 - ExteriorAlgebra.ι R w *
        CliffordAlgebra.contractLeft (Q := 0) f (H.coeff ij.2)
  rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι, Algebra.smul_def]

omit [Algebra ℚ R] in
/-- The signed deletion formula for a finite ordered family of odd series
whose contractions are scalar series. -/
theorem contractSeries_ordered_product (f : Module.Dual R M) (q : ℕ)
    (G : Fin (q + 1) → PowerSeries (ExteriorAlgebra R M))
    (V : Fin (q + 1) → PowerSeries (ExteriorAlgebra R M))
    (hV : ∀ j, V j ∈ Set.range (PowerSeries.map (algebraMap R (ExteriorAlgebra R M))))
    (hG : ∀ j i, (G j).coeff i ∈ LinearMap.range (ExteriorAlgebra.ι R (M := M)))
    (hd : ∀ j, contractSeries f (G j) = V j) :
    contractSeries f (List.ofFn G).prod =
      ∑ j : Fin (q + 1), ((-1 : R) ^ j.val) •
        (V j * (List.ofFn (G ∘ j.succAbove)).prod) := by
  induction q with
  | zero =>
    have hone : (List.ofFn G).prod = G 0 := by simp
    rw [hone, hd]
    simp
  | succ q ih =>
    conv_lhs => rw [List.ofFn_succ, List.prod_cons,
      contractSeries_odd_mul f _ _ (hG 0), hd 0,
      ih (fun j => G j.succ) (fun j => V j.succ) (fun j => hV j.succ)
        (fun j i => hG j.succ i) (fun j => hd j.succ)]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [List.ofFn_succ, List.prod_cons]
    have htail : (fun i : Fin q => (G ∘ j.succ.succAbove) i.succ) =
        (G ∘ Fin.succ) ∘ j.succAbove := by
      funext i
      simp only [Function.comp_apply, Fin.succ_succAbove_succ]
    change -(G 0 * (((-1 : R) ^ j.val) •
      (V j.succ * (List.ofFn ((G ∘ Fin.succ) ∘ j.succAbove)).prod))) = _
    obtain ⟨W, hW⟩ := hV j.succ
    have hcomm : G 0 * V j.succ = V j.succ * G 0 := by
      rw [← hW]
      exact (PowerSeries.scalarSeries_commutes W (G 0)).symm
    rw [mul_smul_comm, ← mul_assoc, hcomm, mul_assoc]
    rw [htail]
    simp only [Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul,
      Function.comp_apply, Fin.succ_succAbove_zero]

/-- A selector jet of a series of generators has coefficients of exterior degree one. -/
theorem selectorJet_iota_mem_range (p : Polynomial ℚ) (b : ℤ) (a i : ℕ) (C : ℕ → M) :
    (((CoefficientSeries.shiftedEuler b)^[a])
      (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b
        (ExteriorAlgebra.iotaSeries (R := R) C))).coeff i ∈
      LinearMap.range (ExteriorAlgebra.ι R (M := M)) := by
  rw [coeff_iterate_evalEuler_map, ExteriorAlgebra.coeff_iotaSeries]
  exact ⟨algebraMap ℚ R (eulerWeight p b a i) • C i, map_smul _ _ _⟩

/-- The differential of the ordered selector product is the deletion expression. -/
theorem contractSeries_selectorBoundary (f : Module.Dual R M) (q : ℕ) (p : Polynomial ℚ)
    (b : ℤ) (C : ℕ → M) (V : PowerSeries R) (hd : ∀ h, f (C h) = V.coeff h) :
    contractSeries f (selectorBoundarySeries q p b (ExteriorAlgebra.iotaSeries (R := R) C)) =
      eulerDeletionSeries q p b b
        (PowerSeries.map (algebraMap R (ExteriorAlgebra R M)) V)
        (ExteriorAlgebra.iotaSeries (R := R) C) := by
  have hjet (j : ℕ) : contractSeries f (((CoefficientSeries.shiftedEuler b)^[j])
      (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b
        (ExteriorAlgebra.iotaSeries (R := R) C))) =
      ((CoefficientSeries.shiftedEuler b)^[j])
        (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b
          (PowerSeries.map (algebraMap R (ExteriorAlgebra R M)) V)) := by
    ext i
    rw [coeff_contractSeries, coeff_iterate_evalEuler_map, coeff_iterate_evalEuler_map,
      map_smul, ExteriorAlgebra.coeff_iotaSeries, CliffordAlgebra.contractLeft_ι, hd,
      PowerSeries.coeff_map]
  have hrange (j : ℕ) : ((CoefficientSeries.shiftedEuler b)^[j])
      (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b
        (PowerSeries.map (algebraMap R (ExteriorAlgebra R M)) V)) ∈
      Set.range (PowerSeries.map (algebraMap R (ExteriorAlgebra R M))) := by
    refine ⟨((CoefficientSeries.shiftedEuler b)^[j])
      (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b V), ?_⟩
    ext i
    rw [PowerSeries.coeff_map, coeff_iterate_evalEuler_map, coeff_iterate_evalEuler_map,
      PowerSeries.coeff_map, smul_eq_mul, map_mul, Algebra.smul_def]
  exact contractSeries_ordered_product f q _ _ (fun j => hrange j.val)
    (fun j i => selectorJet_iota_mem_range p b j.val i C) (fun j => hjet j.val)

omit [Algebra ℚ R] in
/-- The coefficient of an ordered product of weighted odd series. -/
theorem coeff_weightedProduct {q : ℕ} (c : Fin q → ℕ → R) (A : ℕ → M) (D L : ℕ)
    (hDL : D < L) :
    ((List.ofFn (fun a => weightedOddSeries (c a) A)).prod).coeff D =
      alternatingDeficitCoefficient L 0 D c A := by
  rw [CoefficientSeries.coeff_orderedProduct_eq_sum_fin _ D L hDL, alternatingDeficitCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  have hprod : (List.ofFn (fun a => (weightedOddSeries (c a) A).coeff (i a).val)).prod =
      oddTupleTerm c A (fun a => (i a).val) := by
    simp only [weightedOddSeries, PowerSeries.coeff_mk]
    rw [← ExteriorAlgebra.ιMulti_apply]
    exact (ExteriorAlgebra.ιMulti R q).map_smul_univ
      (fun a => c a (i a).val) (fun a => A (i a).val)
  rw [hprod, zero_add]

/-- The ordered selector product of a series of generators, in weighted form. -/
theorem selectorBoundarySeries_iota (q : ℕ) (p : Polynomial ℚ) (b : ℤ) (C : ℕ → M) :
    selectorBoundarySeries q p b (ExteriorAlgebra.iotaSeries (R := R) C) =
      (List.ofFn (fun a : Fin (q + 1) =>
        weightedOddSeries (fun t => algebraMap ℚ R (eulerWeight p b a.val t)) C)).prod := by
  have h : ExteriorAlgebra.iotaSeries (R := R) C = weightedOddSeries (fun _ => (1 : R)) C := by
    ext t
    simp [weightedOddSeries]
  rw [selectorBoundarySeries, h]
  simp only [iterate_evalEuler_weightedOddSeries]

/-- Evaluating the selector at an unwanted index kills every jet coefficient. -/
theorem eulerWeight_selector_eq_zero (b : ℤ) (k a t : ℕ) (T : Finset ℕ)
    (ht : t < k) (htT : t ∉ T) : eulerWeight (selector b k T) b a t = 0 := by
  rw [eulerWeight, eval_selector_eq_zero b k t T ht htT, mul_zero]

omit [Algebra ℚ R] in
/-- The tuple-level alternative behind the coefficient splitting: a nonzero term
with an index at least `m` uses no unselected index below `m`. -/
theorem oddTupleTerm_eq_zero_of_large {q : ℕ} (m k : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range k) (hq : q = T.card) (c : Fin (q + 1) → ℕ → R) (A : ℕ → M)
    (hc : ∀ a t, t < k → t ∉ T → c a t = 0) (v : Fin (q + 1) → ℕ)
    (hsum : ∑ a, v a = m + ∑ t ∈ T, t) (a₀ a₁ : Fin (q + 1)) (ha₀ : m ≤ v a₀)
    (ha₁ : v a₁ < m) (ha₁T : v a₁ ∉ T) : oddTupleTerm c A v = 0 := by
  classical
  by_contra hne
  have hinj : Function.Injective v := by
    by_contra hinj
    exact hne (oddTupleTerm_eq_zero_of_not_injective c A v hinj)
  have hsupport : ∀ a, v a < k → v a ∈ T := by
    intro a hak
    by_contra hat
    exact hne (oddTupleTerm_eq_zero_of_coefficient c A v a (hc a (v a) hak hat))
  have hne₀₁ : a₁ ≠ a₀ := fun h => by
    rw [h] at ha₁
    omega
  let S := (Finset.univ.erase a₀).image v
  have hcard : S.card = T.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, ← hq]
    rfl
  have hSsum : ∑ i ∈ S, i ≤ ∑ t ∈ T, t := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    have hsplit := Finset.add_sum_erase Finset.univ v (Finset.mem_univ a₀)
    omega
  have hST : S = T := by
    apply support_eq_selected_of_sum_le k T S hT hcard _ hSsum
    intro i hi hik
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact hsupport a hik
  apply ha₁T
  rw [← hST]
  exact Finset.mem_image.mpr ⟨a₁, Finset.mem_erase.mpr ⟨hne₀₁, Finset.mem_univ _⟩, rfl⟩

/-- The selected coefficient of the ordered product. The first summand uses only
deficits below `m`. The second has the generator at deficit `m` as its first
factor, followed by the selected generators in increasing order of deficit. -/
theorem selectorBoundarySeries_coeff_split {q : ℕ} (b : ℤ) (m k : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range k) (hq : q = T.card) (hkm : k ≤ m) (C : ℕ → M) :
    (selectorBoundarySeries q (selector b k T) b
        (ExteriorAlgebra.iotaSeries (R := R) C)).coeff (m + ∑ t ∈ T, t) =
      (selectorBoundarySeries q (selector b k T) b (ExteriorAlgebra.iotaSeries (R := R)
        (fun h => if h < m then C h else 0))).coeff (m + ∑ t ∈ T, t) +
      algebraMap ℚ R (transferScalar m k T) •
        (ExteriorAlgebra.ι R (C m) * ExteriorAlgebra.ιMulti R q
          (fun j => C (T.orderEmbOfFin hq.symm j))) := by
  classical
  set p := selector b k T with hp
  set D := m + ∑ t ∈ T, t with hD
  let L := D + 1
  let c : Fin (q + 1) → ℕ → R := fun a t => algebraMap ℚ R (eulerWeight p b a.val t)
  let c' : Fin (q + 1) → ℕ → R := fun a t => if t < m ∧ t ∉ T then 0 else c a t
  have hmT : m ∉ T := fun h => by
    have := Finset.mem_range.mp (hT h)
    omega
  have hcZero : ∀ a t, t < k → t ∉ T → c a t = 0 := by
    intro a t ht htT
    simp only [c, hp, eulerWeight_selector_eq_zero b k a.val t T ht htT, map_zero]
  rw [selectorBoundarySeries_iota, selectorBoundarySeries_iota,
    coeff_weightedProduct _ _ D L (Nat.lt_succ_self D),
    coeff_weightedProduct _ _ D L (Nat.lt_succ_self D)]
  have hsplit : alternatingDeficitCoefficient L 0 D c C =
      alternatingDeficitCoefficient L 0 D c (fun h => if h < m then C h else 0) +
        alternatingDeficitCoefficient L 0 D c' C := by
    simp only [alternatingDeficitCoefficient, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    set v : Fin (q + 1) → ℕ := fun a => (i a).val with hv
    by_cases hsum : 0 + ∑ a, v a = D
    · simp only [if_pos hsum]
      rw [zero_add] at hsum
      by_cases hsmall : ∀ a, v a < m
      · have hleft : oddTupleTerm c (fun h => if h < m then C h else 0) v = oddTupleTerm c C v := by
          simp only [oddTupleTerm]
          congr 2
          funext a
          simp [hsmall a]
        have hright : oddTupleTerm c' C v = 0 := by
          by_cases hinj : Function.Injective v
          · have hex : ∃ a, v a ∉ T := by
              by_contra hall
              push Not at hall
              have hle : (Finset.univ.image v).card ≤ T.card := by
                apply Finset.card_le_card
                intro t ht
                obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ht
                exact hall a
              rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hle
              omega
            obtain ⟨a, ha⟩ := hex
            apply oddTupleTerm_eq_zero_of_coefficient c' C v a
            simp only [c', if_pos (And.intro (hsmall a) ha)]
          · exact oddTupleTerm_eq_zero_of_not_injective c' C v hinj
        rw [hleft, hright, add_zero]
      · push Not at hsmall
        obtain ⟨a₀, ha₀⟩ := hsmall
        have hleft : oddTupleTerm c (fun h => if h < m then C h else 0) v = 0 := by
          rw [oddTupleTerm, (ExteriorAlgebra.ιMulti R (q + 1)).map_coord_zero a₀ (by
            simp [Nat.not_lt.mpr ha₀]), smul_zero]
        rw [hleft, zero_add]
        by_cases hbad : ∃ a₁, v a₁ < m ∧ v a₁ ∉ T
        · obtain ⟨a₁, h₁, h₂⟩ := hbad
          rw [oddTupleTerm_eq_zero_of_large m k T hT hq c C hcZero v hsum a₀ a₁ ha₀ h₁ h₂]
          exact (oddTupleTerm_eq_zero_of_coefficient c' C v a₁ (by
            simp only [c', if_pos (And.intro h₁ h₂)])).symm
        · push Not at hbad
          simp only [oddTupleTerm]
          congr 1
          apply Finset.prod_congr rfl
          intro a _
          simp only [c']
          rw [if_neg (fun h => h.2 (hbad a h.1))]
    · simp only [if_neg hsum, add_zero]
  rw [hsplit]
  congr 1
  set T' := insert m T with hT'
  have hT'range : T' ⊆ Finset.range (m + 1) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
    · have := Finset.mem_range.mp (hT ht)
      exact Finset.mem_range.mpr (by omega)
  have hq' : q + 1 = T'.card := by rw [hT', Finset.card_insert_of_notMem hmT, ← hq]
  have hD' : D = ∑ t ∈ T', t := by rw [hT', Finset.sum_insert hmT]
  have hc' : ∀ a t, t < m + 1 → t ∉ T' → c' a t = 0 := by
    intro a t ht htT
    simp only [Finset.mem_insert, hT', not_or] at htT
    simp only [c', if_pos (And.intro (by omega : t < m) htT.2)]
  rw [hD', alternatingDeficitCoefficient_eq_selected (m + 1) L T' hT'range hq' c' C hc']
  let ν : Fin (q + 1) → ℕ := Fin.cons m (fun j => T.orderEmbOfFin hq.symm j)
  have hmL : m < L := by simp only [L, hD]; omega
  have hTL : T ⊆ Finset.range L := by
    intro t ht
    have := Finset.mem_range.mp (hT ht)
    exact Finset.mem_range.mpr (by omega)
  have hrow (a : Fin (q + 1)) :
      (∑ t : Fin L, (if t.val ∈ T' then c' a t.val else 0) • C t.val) =
        ∑ j : Fin (q + 1), c a (ν j) • C (ν j) := by
    have hsplitIte (t : Fin L) : (if t.val ∈ T' then c' a t.val else 0) • C t.val =
        (if t.val = m then c a m • C m else 0) +
          (if t.val ∈ T then c a t.val • C t.val else 0) := by
      by_cases h₁ : t.val = m
      · have h₂ : t.val ∉ T := h₁ ▸ hmT
        simp [h₁, hT', c', hmT]
      · by_cases h₂ : t.val ∈ T
        · simp [h₁, h₂, hT', c']
        · simp [h₁, h₂, hT']
    have hν : (∑ j : Fin (q + 1), c a (ν j) • C (ν j)) = c a m • C m +
        ∑ j : Fin q, c a (T.orderEmbOfFin hq.symm j) • C (T.orderEmbOfFin hq.symm j) :=
      Fin.sum_univ_succ _
    rw [Finset.sum_congr rfl (fun t _ => hsplitIte t), Finset.sum_add_distrib,
      sum_selected_eq_ordered L T hq hTL (fun t => c a t • C t), hν]
    congr 1
    rw [Finset.sum_eq_single (⟨m, hmL⟩ : Fin L)]
    · simp
    · intro t _ ht
      rw [if_neg (fun h => ht (Fin.ext h))]
    · simp
  simp_rw [hrow]
  have hcomb := iotaMulti_linear_combinations (Matrix.of fun a j => c a (ν j)) (fun j => C (ν j))
  simp only [Matrix.of_apply] at hcomb
  rw [hcomb]
  have hdet : (Matrix.of fun a j => c a (ν j)).det = algebraMap ℚ R (transferScalar m k T) := by
    rw [← det_eulerSelectorMatrix_eq_transferScalar b m k T hT hq, RingHom.map_det]
    congr 1
    ext a j
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, c, eulerSelectorMatrix,
      eulerWeight, selectedEigenvalues, ν, hp]
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp
  rw [hdet]
  congr 1
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  rfl

omit [Algebra ℚ R] in
/-- A ring map carrying generators to generators carries ordered exterior products along. -/
theorem map_iotaMulti {R' M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']
    (g : ExteriorAlgebra R M →+* ExteriorAlgebra R' M') (q : ℕ) (v : Fin q → M) (v' : Fin q → M')
    (h : ∀ j, g (ExteriorAlgebra.ι R (v j)) = ExteriorAlgebra.ι R' (v' j)) :
    g (ExteriorAlgebra.ιMulti R q v) = ExteriorAlgebra.ιMulti R' q v' := by
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  exact congrArg List.ofFn (funext h)

/-- A ring map compatible with rational scalars carries the ordered selector product along. -/
theorem map_selectorBoundarySeries {R' M' : Type*} [CommRing R'] [Algebra ℚ R']
    [AddCommGroup M'] [Module R' M']
    (g : ExteriorAlgebra R M →+* ExteriorAlgebra R' M')
    (hg : ∀ (w : ℚ) (x : ExteriorAlgebra R M),
      g (algebraMap ℚ R w • x) = algebraMap ℚ R' w • g x)
    (C : ℕ → M) (C' : ℕ → M')
    (hC : ∀ h, g (ExteriorAlgebra.ι R (C h)) = ExteriorAlgebra.ι R' (C' h))
    (q : ℕ) (p : Polynomial ℚ) (b : ℤ) :
    PowerSeries.map g (selectorBoundarySeries q p b (ExteriorAlgebra.iotaSeries (R := R) C)) =
      selectorBoundarySeries q p b (ExteriorAlgebra.iotaSeries (R := R') C') := by
  simp only [selectorBoundarySeries, map_list_prod, List.map_ofFn]
  congr 2
  funext a
  ext t
  simp only [Function.comp_apply, PowerSeries.coeff_map, coeff_iterate_evalEuler_map, hg,
    ExteriorAlgebra.coeff_iotaSeries, hC]

end TorusLinkHomology.CoefficientSelector
