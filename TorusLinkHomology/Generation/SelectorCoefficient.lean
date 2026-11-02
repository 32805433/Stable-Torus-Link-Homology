import TorusLinkHomology.Generation.Selector
import TorusLinkHomology.Generation.OrderedPowerSeries
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# Exact support selection for exceptional coefficients

The deficit equation, exterior distinctness, and the roots of the selector
exclude every tuple except the prescribed selected set. The lemmas retain
the order of exterior factors and apply before passing to homology.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.CoefficientSelector

/-- ET-06: among sets of the prescribed size supported on `T` and indices at
least `k`, the selected set uniquely minimizes the sum of the indices. -/
theorem support_eq_selected_of_sum_le (k : ℕ) (T S : Finset ℕ)
    (hT : T ⊆ Finset.range k) (hcard : S.card = T.card)
    (hsupport : ∀ i ∈ S, i < k → i ∈ T)
    (hsum : ∑ i ∈ S, i ≤ ∑ i ∈ T, i) : S = T := by
  by_contra hne
  have hnot : ¬T ⊆ S := by
    intro h
    exact hne (Finset.eq_of_subset_of_card_le h hcard.le).symm
  have hnonempty : (T \ S).Nonempty := Finset.sdiff_nonempty.mpr hnot
  have hcards : (S \ T).card = (T \ S).card := Finset.card_sdiff_comm hcard
  have hlarge : (S \ T).card * k ≤ ∑ i ∈ S \ T, i := by
    calc
      _ = ∑ _i ∈ S \ T, k := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => by
        have hm := Finset.mem_sdiff.mp hi
        exact Nat.le_of_not_gt (fun hik => hm.2 (hsupport i hm.1 hik))
  have hsmall : ∑ i ∈ T \ S, i < (T \ S).card * k := by
    calc
      _ < ∑ _i ∈ T \ S, k := Finset.sum_lt_sum_of_nonempty hnonempty fun i hi =>
        Finset.mem_range.mp (hT (Finset.mem_sdiff.mp hi).1)
      _ = _ := by simp
  have hS := Finset.sum_inter_add_sum_sdiff S T (fun i : ℕ => i)
  have hT' := Finset.sum_inter_add_sum_sdiff T S (fun i : ℕ => i)
  rw [Finset.inter_comm T S] at hT'
  rw [hcards] at hlarge
  omega

/-- ET-06 with an additional nonnegative scalar deficit: that deficit must
be zero, and the odd coefficient indices must be exactly the selected set. -/
theorem tuple_eq_selected_of_deficit (k q j : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range k) (hq : q = T.card) (i : Fin q → ℕ)
    (hi : Function.Injective i) (hsupport : ∀ a, i a < k → i a ∈ T)
    (hdeficit : j + ∑ a : Fin q, i a = ∑ t ∈ T, t) :
    j = 0 ∧ Finset.univ.image i = T := by
  have hsum : ∑ t ∈ Finset.univ.image i, t = ∑ a : Fin q, i a := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hi hab
  have hcard : (Finset.univ.image i).card = T.card := by
    rw [Finset.card_image_of_injective _ hi]
    simpa using hq
  have hselected : Finset.univ.image i = T := by
    apply support_eq_selected_of_sum_le k T _ hT hcard
    · intro t ht htk
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ht
      exact hsupport a htk
    · rw [hsum]
      omega
  refine ⟨?_, hselected⟩
  rw [hselected] at hsum
  omega

section AlternatingTerms

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- One ordered term in the finite coefficient expansion, with its scalar
factors collected. -/
def oddTupleTerm {q : ℕ} (c : Fin q → ℕ → R) (A : ℕ → M) (i : Fin q → ℕ) :
    ExteriorAlgebra R M :=
  (∏ a : Fin q, c a (i a)) • ExteriorAlgebra.ιMulti R q (A ∘ i)

/-- A repeated odd coefficient forces the ordered exterior term to vanish. -/
theorem oddTupleTerm_eq_zero_of_not_injective {q : ℕ}
    (c : Fin q → ℕ → R) (A : ℕ → M) (i : Fin q → ℕ)
    (hi : ¬Function.Injective i) : oddTupleTerm c A i = 0 := by
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, i a = i b ∧ a ≠ b := by
    unfold Function.Injective at hi
    push Not at hi
    exact hi
  rw [oddTupleTerm, (ExteriorAlgebra.ιMulti R q).map_eq_zero_of_eq (A ∘ i)
    (congrArg A hab) hne, smul_zero]

/-- A zero selector value removes the term before any exterior reordering. -/
theorem oddTupleTerm_eq_zero_of_coefficient {q : ℕ}
    (c : Fin q → ℕ → R) (A : ℕ → M) (i : Fin q → ℕ)
    (a : Fin q) (ha : c a (i a) = 0) : oddTupleTerm c A i = 0 := by
  rw [oddTupleTerm, Finset.prod_eq_zero (Finset.mem_univ a) ha, zero_smul]

/-- ET-06 at the level of each actual exterior summand. If the total deficit
is the selected one, every nonzero term has zero scalar deficit and exactly
the selected odd coefficient indices. -/
theorem oddTupleTerm_support_of_ne_zero {q : ℕ} (k j : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range k) (hq : q = T.card)
    (c : Fin q → ℕ → R) (A : ℕ → M)
    (hc : ∀ a t, t < k → t ∉ T → c a t = 0) (i : Fin q → ℕ)
    (hdeficit : j + ∑ a : Fin q, i a = ∑ t ∈ T, t)
    (hne : oddTupleTerm c A i ≠ 0) : j = 0 ∧ Finset.univ.image i = T := by
  apply tuple_eq_selected_of_deficit k q j T hT hq i
  · by_contra hi
    exact hne (oddTupleTerm_eq_zero_of_not_injective c A i hi)
  · intro a ha
    by_contra hat
    exact hne (oddTupleTerm_eq_zero_of_coefficient c A i a (hc a (i a) ha hat))
  · exact hdeficit

/-- The exact finite coefficient sum, with a separate deficit for the even
factor. The cutoff `L` only enumerates a finite range of odd coefficients. -/
def alternatingDeficitCoefficient {q : ℕ} (L j D : ℕ)
    (c : Fin q → ℕ → R) (A : ℕ → M) : ExteriorAlgebra R M :=
  ∑ i : Fin q → Fin L,
    if j + ∑ a : Fin q, (i a).val = D then oddTupleTerm c A (fun a => (i a).val) else 0

/-- Finite multilinearity gives the ordered exterior coefficient expansion. -/
theorem iotaMulti_sum_eq_sum_oddTupleTerm {q : ℕ} (L : ℕ)
    (c : Fin q → ℕ → R) (A : ℕ → M) :
    ExteriorAlgebra.ιMulti R q (fun a => ∑ t : Fin L, c a t.val • A t.val) =
      ∑ i : Fin q → Fin L, oddTupleTerm c A (fun a => (i a).val) := by
  change (ExteriorAlgebra.ιMulti R q).toMultilinearMap
    (fun a => ∑ t : Fin L, c a t.val • A t.val) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (ExteriorAlgebra.ιMulti R q).map_smul_univ
    (fun a => c a (i a).val) (fun a => A (i a).val)

/-- Filtering the allowed index set either keeps an entire tuple or kills it. -/
theorem oddTupleTerm_filter {q : ℕ} (T : Finset ℕ)
    (c : Fin q → ℕ → R) (A : ℕ → M) (i : Fin q → ℕ) :
    oddTupleTerm (fun a t => if t ∈ T then c a t else 0) A i =
      if ∀ a, i a ∈ T then oddTupleTerm c A i else 0 := by
  by_cases h : ∀ a, i a ∈ T
  · rw [if_pos h]
    unfold oddTupleTerm
    congr 1
    apply Finset.prod_congr rfl
    intro a _
    simp [h a]
  · rw [if_neg h]
    obtain ⟨a, ha⟩ := not_forall.mp h
    exact oddTupleTerm_eq_zero_of_coefficient _ A i a (if_neg ha)

/-- An ordered alternating product of linear combinations transforms by the
row determinant, without requiring commutativity of the target algebra. -/
theorem iotaMulti_linear_combinations {q : ℕ} (B : Matrix (Fin q) (Fin q) R)
    (v : Fin q → M) :
    ExteriorAlgebra.ιMulti R q (fun a => ∑ j, B a j • v j) =
      B.det • ExteriorAlgebra.ιMulti R q v := by
  let e := Pi.basisFun R (Fin q)
  let f : M [⋀^Fin q]→ₗ[R] ExteriorAlgebra R M := ExteriorAlgebra.ιMulti R q
  let g := f.compLinearMap (e.constr R v)
  have hg : g = e.det.smulRight (f v) := by
    apply Module.Basis.ext_alternating e
    intro i hi
    let σ : Equiv.Perm (Fin q) := Equiv.ofBijective i
      (Finite.injective_iff_bijective.mp hi)
    change g (e ∘ σ) = (e.det.smulRight (f v)) (e ∘ σ)
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    simp [g, f, AlternatingMap.compLinearMap_apply, Module.Basis.det_self]
  have hv := DFunLike.congr_fun hg B
  change f (fun a => e.constr R v (B a)) = e.det B • f v at hv
  rw [show e.det B = B.det from Pi.basisFun_det_apply B] at hv
  simpa [e, f, Module.Basis.constr_apply_fintype] using hv

/-- ET-06: exact finite coefficient extraction. The only surviving tuples
are permutations of the selected indices, and multilinearity collects them
into one alternating product of the selected row vectors. -/
theorem alternatingDeficitCoefficient_eq_selected {q : ℕ} (k L : ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q = T.card)
    (c : Fin q → ℕ → R) (A : ℕ → M)
    (hc : ∀ a t, t < k → t ∉ T → c a t = 0) :
    alternatingDeficitCoefficient L 0 (∑ t ∈ T, t) c A =
      ExteriorAlgebra.ιMulti R q
        (fun a => ∑ t : Fin L, (if t.val ∈ T then c a t.val else 0) • A t.val) := by
  rw [iotaMulti_sum_eq_sum_oddTupleTerm L (fun a t => if t ∈ T then c a t else 0) A]
  unfold alternatingDeficitCoefficient
  apply Finset.sum_congr rfl
  intro i _
  rw [oddTupleTerm_filter]
  let v : Fin q → ℕ := fun a => (i a).val
  change (if 0 + ∑ a, v a = ∑ t ∈ T, t then oddTupleTerm c A v else 0) =
    if ∀ a, v a ∈ T then oddTupleTerm c A v else 0
  by_cases hall : ∀ a, v a ∈ T
  · rw [if_pos hall]
    by_cases hinj : Function.Injective v
    · have heq : Finset.univ.image v = T := by
        apply Finset.eq_of_subset_of_card_le
        · intro t ht
          obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ht
          exact hall a
        · rw [Finset.card_image_of_injective _ hinj]
          simp [hq]
      have hsum : ∑ a : Fin q, v a = ∑ t ∈ T, t := by
        rw [← heq, Finset.sum_image]
        exact fun a _ b _ hab => hinj hab
      simp [hsum]
    · rw [oddTupleTerm_eq_zero_of_not_injective c A v hinj]
      simp
  · rw [if_neg hall]
    split_ifs with hdeficit
    · by_contra hne
      have heq := (oddTupleTerm_support_of_ne_zero k 0 T hT hq c A hc v hdeficit hne).2
      apply hall
      intro a
      rw [← heq]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    · rfl

/-- Reindex the selected row by its increasing enumeration. -/
theorem sum_selected_eq_ordered {q : ℕ} (L : ℕ) (T : Finset ℕ)
    (hq : q = T.card) (hTL : T ⊆ Finset.range L) (f : ℕ → M) :
    (∑ t : Fin L, if t.val ∈ T then f t.val else 0) =
      ∑ j : Fin q, f (T.orderEmbOfFin hq.symm j) := by
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => if t ∈ T then f t else 0), Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hTL]
  conv_lhs => rw [← T.image_orderEmbOfFin_univ hq.symm]
  rw [Finset.sum_image]
  exact fun a _ b _ h => (T.orderEmbOfFin hq.symm).injective h

/-- The odd coefficient series with scalar Euler weights. -/
def weightedOddSeries (c : ℕ → R) (A : ℕ → M) :
    PowerSeries (ExteriorAlgebra R M) :=
  PowerSeries.mk fun t => ExteriorAlgebra.ι R (c t • A t)

end AlternatingTerms

/-- The coefficient of an Euler iterate of a polynomial-selector output. -/
def eulerWeight (p : Polynomial ℚ) (b : ℤ) (a t : ℕ) : ℚ :=
  ((b : ℚ) - (t : ℚ)) ^ a * p.eval ((b : ℚ) - (t : ℚ))

/-- The even eigenvalue followed by the selected odd eigenvalues. -/
def selectedEigenvalues {q : ℕ} (b ell : ℤ) (T : Finset ℕ) (hq : q = T.card) :
    Fin (q + 1) → ℚ :=
  Fin.cons (ell : ℚ) (fun j => (b : ℚ) - (T.orderEmbOfFin hq.symm j : ℕ))

/-- The determinant that occurs before simplifying the transfer scalar. -/
def eulerSelectorMatrix {q : ℕ} (p : Polynomial ℚ) (b ell : ℤ)
    (T : Finset ℕ) (hq : q = T.card) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℚ :=
  fun a j => selectedEigenvalues b ell T hq j ^ a.val *
    p.eval (selectedEigenvalues b ell T hq j)

/-- ET-07's Vandermonde factorization, with the exact exterior-order sign. -/
theorem det_eulerSelectorMatrix {q : ℕ} (p : Polynomial ℚ) (b ell : ℤ)
    (T : Finset ℕ) (hq : q = T.card) :
    (eulerSelectorMatrix p b ell T hq).det =
      (∏ j, p.eval (selectedEigenvalues b ell T hq j)) *
        ∏ i : Fin (q + 1), ∏ j ∈ Finset.Ioi i,
          (selectedEigenvalues b ell T hq j - selectedEigenvalues b ell T hq i) :=
  det_euler_matrix p (selectedEigenvalues b ell T hq)

/-- Products may be indexed by the increasing enumeration of a finite set. -/
theorem prod_ordered_eq_prod {q : ℕ} (T : Finset ℕ) (hq : q = T.card)
    (f : ℕ → ℚ) :
    (∏ j : Fin q, f (T.orderEmbOfFin hq.symm j)) = ∏ t ∈ T, f t := by
  conv_rhs => rw [← T.image_orderEmbOfFin_univ hq.symm]
  rw [Finset.prod_image]
  exact fun a _ b _ h => (T.orderEmbOfFin hq.symm).injective h

/-- The ordered pairwise factor equals the finite-set form of the transfer
scalar; strict increase fixes the exterior sign. -/
theorem pairFactor_eq_ordered {q : ℕ} (T : Finset ℕ) (hq : q = T.card) :
    pairFactor T = ∏ i : Fin q, ∏ j ∈ Finset.Ioi i,
      (((T.orderEmbOfFin hq.symm i : ℕ) : ℚ) - (T.orderEmbOfFin hq.symm (j : Fin q) : ℕ)) := by
  unfold pairFactor
  rw [← prod_ordered_eq_prod T hq
    (fun i => ∏ j ∈ T.filter (i < ·), ((i : ℚ) - j))]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_filter, ← prod_ordered_eq_prod T hq
    (fun j => if T.orderEmbOfFin hq.symm i < j then
      ((T.orderEmbOfFin hq.symm i : ℕ) : ℚ) - j else 1)]
  simp only [(T.orderEmbOfFin hq.symm).lt_iff_lt]
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

/-- The even selector evaluation contributes precisely the omitted falling
factors and the sign `(-1)^(k-q)`. -/
theorem eval_selector_even (b : ℤ) (m k : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range k) :
    (selector b k T).eval ((b : ℚ) - (m : ℚ)) =
      (-1 : ℚ) ^ (k - T.card) *
        ∏ a ∈ Finset.range k \ T, ((m : ℚ) - (a : ℚ)) := by
  rw [eval_selector]
  have h (a : ℕ) : (a : ℚ) - m = -((m : ℚ) - a) := by ring
  simp_rw [h]
  rw [Finset.prod_neg, Finset.card_sdiff_of_subset hT, Finset.card_range]

/-- ET-07: the selected Euler determinant is exactly the transfer scalar,
including its sign. No lower bound on `m` is needed for this identity. -/
theorem det_eulerSelectorMatrix_eq_transferScalar {q : ℕ} (b : ℤ) (m k : ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q = T.card) :
    (eulerSelectorMatrix (selector b k T) b (b - m) T hq).det =
      transferScalar m k T := by
  rw [det_eulerSelectorMatrix]
  simp only [selectedEigenvalues, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.prod_Ioi_zero, Fin.prod_Ioi_succ, Int.cast_sub, Int.cast_natCast]
  have hdiff (s t : ℕ) : ((b : ℚ) - t) - ((b : ℚ) - s) = (s : ℚ) - t := by ring
  simp_rw [hdiff, eval_selector_even b m k T hT, eval_selector]
  rw [prod_ordered_eq_prod T hq (fun t => ∏ a ∈ Finset.range k \ T, ((a : ℚ) - t)),
    prod_ordered_eq_prod T hq (fun t => (m : ℚ) - t), ← pairFactor_eq_ordered T hq]
  change ((-1 : ℚ) ^ (k - T.card) *
      (∏ a ∈ Finset.range k \ T, ((m : ℚ) - a)) * crossFactor k T) *
      ((∏ t ∈ T, ((m : ℚ) - t)) * pairFactor T) = _
  have hfall : (∏ a ∈ Finset.range k \ T, ((m : ℚ) - a)) *
      (∏ t ∈ T, ((m : ℚ) - t)) = fallingFactor m k :=
    Finset.prod_sdiff hT
  unfold transferScalar
  rw [← hfall]
  ring

section RationalAlgebra

variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Module R M]

/-- Euler-selector weights are the actual eigenvalues of the iterated
shifted Euler operator, also after changing the coefficient ring. -/
theorem coeff_iterate_evalEuler_map {E : Type*} [Ring E] [Algebra R E]
    (p : Polynomial ℚ) (b : ℤ) (a t : ℕ) (f : PowerSeries E) :
    (((CoefficientSeries.shiftedEuler b)^[a])
      (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b f)).coeff t =
      algebraMap ℚ R (eulerWeight p b a t) • f.coeff t := by
  rw [CoefficientSeries.coeff_iterate_shiftedEuler, CoefficientSeries.coeff_evalEuler,
    ← Int.cast_smul_eq_zsmul R, Int.cast_pow, smul_smul]
  have hcast : ((b - (t : ℤ) : ℤ) : R) =
      algebraMap ℚ R ((b : ℚ) - (t : ℚ)) := by simp
  rw [hcast, Polynomial.eval_map_apply, ← map_pow, ← map_mul]
  rfl

/-- Euler operations on the odd series preserve its exterior degree one. -/
theorem iterate_evalEuler_weightedOddSeries (p : Polynomial ℚ) (b : ℤ) (a : ℕ)
    (A : ℕ → M) :
    ((CoefficientSeries.shiftedEuler b)^[a])
      (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b
        (weightedOddSeries (fun _ => (1 : R)) A)) =
      weightedOddSeries (fun t => algebraMap ℚ R (eulerWeight p b a t)) A := by
  ext t
  rw [coeff_iterate_evalEuler_map]
  simp [weightedOddSeries]

/-- The Euler-selector deletion expression, keeping the odd factors in
their increasing derivative order after the indicated deletion. -/
def eulerDeletionSeries (q : ℕ) (p : Polynomial ℚ) (b ell : ℤ)
    (V C : PowerSeries (ExteriorAlgebra R M)) : PowerSeries (ExteriorAlgebra R M) :=
  ∑ a : Fin (q + 1), ((-1 : R) ^ a.val) •
    (((CoefficientSeries.shiftedEuler ell)^[a.val])
      (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) ell V) *
      (List.ofFn (fun j : Fin q =>
        ((CoefficientSeries.shiftedEuler b)^[(a.succAbove j).val])
          (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b C))).prod)

end RationalAlgebra

end TorusLinkHomology.CoefficientSelector
