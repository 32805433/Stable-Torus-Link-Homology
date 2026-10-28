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

/-- All positive deficits of the even factor vanish in the selected
coefficient. Thus no unwanted even coefficient can survive. -/
theorem alternatingDeficitCoefficient_eq_zero_of_pos {q : ℕ} (k L j : ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q = T.card)
    (c : Fin q → ℕ → R) (A : ℕ → M)
    (hc : ∀ a t, t < k → t ∉ T → c a t = 0) (hj : 0 < j) :
    alternatingDeficitCoefficient L j (∑ t ∈ T, t) c A = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hdeficit
  · by_contra hne
    have h := oddTupleTerm_support_of_ne_zero k j T hT hq c A hc
      (fun a => (i a).val) hdeficit hne
    omega
  · rfl

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

/-- ET-06/07: the exact finite coefficient is the selected determinant
multiplying the increasingly ordered exterior product. -/
theorem alternatingDeficitCoefficient_eq_det {q : ℕ} (k L : ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q = T.card)
    (hTL : T ⊆ Finset.range L) (c : Fin q → ℕ → R) (A : ℕ → M)
    (hc : ∀ a t, t < k → t ∉ T → c a t = 0) :
    alternatingDeficitCoefficient L 0 (∑ t ∈ T, t) c A =
      (Matrix.of (fun a j : Fin q => c a (T.orderEmbOfFin hq.symm j))).det •
        ExteriorAlgebra.ιMulti R q (fun j => A (T.orderEmbOfFin hq.symm j)) := by
  rw [alternatingDeficitCoefficient_eq_selected k L T hT hq c A hc]
  have hs (a : Fin q) :
      (∑ t : Fin L, (if t.val ∈ T then c a t.val else 0) • A t.val) =
        ∑ j : Fin q, c a (T.orderEmbOfFin hq.symm j) •
          A (T.orderEmbOfFin hq.symm j) := by
    simp_rw [ite_smul, zero_smul]
    exact sum_selected_eq_ordered L T hq hTL (fun t => c a t • A t)
  simp_rw [hs]
  exact iotaMulti_linear_combinations _ _

/-- The finite coefficient of the signed deletion expression: `e` gives the
even-factor coefficients and `c` gives the scalar weights of odd factors. -/
def deletionDeficitCoefficient {q : ℕ} (L J D : ℕ)
    (e c : Fin (q + 1) → ℕ → R) (A : ℕ → M) : ExteriorAlgebra R M :=
  ∑ a : Fin (q + 1), ∑ j : Fin (J + 1),
    ((-1 : R) ^ a.val * e a j.val) •
      alternatingDeficitCoefficient L j.val D (fun b => c (a.succAbove b)) A

/-- The selected matrix has the surviving even coefficient in column zero,
followed by the selected odd coefficients in increasing order. -/
def selectedMatrix {q : ℕ} (T : Finset ℕ) (hq : q = T.card)
    (e c : Fin (q + 1) → ℕ → R) : Matrix (Fin (q + 1)) (Fin (q + 1)) R :=
  fun a => Fin.cons (e a 0) (fun j => c a (T.orderEmbOfFin hq.symm j))

/-- ET-07: first-column expansion gives exactly the signed deletion order.
All positive even deficits and all unselected odd indices have vanished. -/
theorem deletionDeficitCoefficient_eq_det {q : ℕ} (k L J : ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q = T.card)
    (hTL : T ⊆ Finset.range L) (e c : Fin (q + 1) → ℕ → R) (A : ℕ → M)
    (hc : ∀ a t, t < k → t ∉ T → c a t = 0) :
    deletionDeficitCoefficient L J (∑ t ∈ T, t) e c A =
      (selectedMatrix T hq e c).det •
        ExteriorAlgebra.ιMulti R q (fun j => A (T.orderEmbOfFin hq.symm j)) := by
  unfold deletionDeficitCoefficient
  have hj (a : Fin (q + 1)) :
      (∑ j : Fin (J + 1), ((-1 : R) ^ a.val * e a j.val) •
        alternatingDeficitCoefficient L j.val (∑ t ∈ T, t)
          (fun b => c (a.succAbove b)) A) =
      ((-1 : R) ^ a.val * e a 0) •
        alternatingDeficitCoefficient L 0 (∑ t ∈ T, t)
          (fun b => c (a.succAbove b)) A := by
    apply Fintype.sum_eq_single (0 : Fin (J + 1))
    intro j hj
    have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj (Fin.ext h))
    rw [alternatingDeficitCoefficient_eq_zero_of_pos k L j.val T hT hq _ A
      (fun b => hc (a.succAbove b)) hjpos, smul_zero]
  simp_rw [hj, alternatingDeficitCoefficient_eq_det k L T hT hq hTL _ A
    (fun b => hc (_))]
  rw [Matrix.det_succ_column_zero, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_smul]
  rfl

/-- A common factor in the even coefficient scales only column zero. -/
theorem selectedMatrix_det_even_mul {q : ℕ} (T : Finset ℕ) (hq : q = T.card)
    (e c : Fin (q + 1) → ℕ → R) (v : ℕ → R) :
    (selectedMatrix T hq (fun a j => v j * e a j) c).det =
      v 0 * (selectedMatrix T hq e c).det := by
  have hmat : selectedMatrix T hq (fun a j => v j * e a j) c =
      (selectedMatrix T hq e c).updateCol 0
        (v 0 • fun a => selectedMatrix T hq e c a 0) := by
    ext a j
    induction j using Fin.cases with
    | zero => simp [selectedMatrix]
    | succ j => simp [selectedMatrix]
  rw [hmat, Matrix.det_updateCol_smul]
  simp

/-- A series of scalar coefficients inside the exterior algebra. -/
def scalarSeries (e : ℕ → R) : PowerSeries (ExteriorAlgebra R M) :=
  PowerSeries.mk fun j => algebraMap R (ExteriorAlgebra R M) (e j)

/-- The odd coefficient series with scalar Euler weights. -/
def weightedOddSeries (c : ℕ → R) (A : ℕ → M) :
    PowerSeries (ExteriorAlgebra R M) :=
  PowerSeries.mk fun t => ExteriorAlgebra.ι R (c t • A t)

/-- The noncommutative power-series convolution is exactly the finite
alternating deficit sum. No completion of the coefficient algebra is used. -/
theorem coeff_scalar_mul_weightedProduct {q : ℕ} (e : ℕ → R)
    (c : Fin q → ℕ → R) (A : ℕ → M) (D L : ℕ) (hDL : D < L) :
    (scalarSeries (M := M) e *
      (List.ofFn (fun a => weightedOddSeries (c a) A)).prod).coeff D =
      ∑ j : Fin L, e j.val • alternatingDeficitCoefficient L j.val D c A := by
  rw [CoefficientSeries.coeff_mul_orderedProduct_eq_sum_fin _ _ D L hDL]
  have hprod (i : Fin q → Fin L) :
      (List.ofFn (fun a => (weightedOddSeries (c a) A).coeff (i a).val)).prod =
        oddTupleTerm c A (fun a => (i a).val) := by
    simp only [weightedOddSeries, PowerSeries.coeff_mk]
    rw [← ExteriorAlgebra.ιMulti_apply]
    exact (ExteriorAlgebra.ιMulti R q).map_smul_univ
      (fun a => c a (i a).val) (fun a => A (i a).val)
  simp_rw [hprod]
  apply Finset.sum_congr rfl
  intro j _
  rw [alternatingDeficitCoefficient, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [scalarSeries, Algebra.smul_def]

/-- The signed deletion expression as an actual ordered power series. -/
def deletionSeries {q : ℕ} (e c : Fin (q + 1) → ℕ → R) (A : ℕ → M) :
    PowerSeries (ExteriorAlgebra R M) :=
  ∑ a : Fin (q + 1), ((-1 : R) ^ a.val) •
    (scalarSeries (M := M) (e a) *
      (List.ofFn (fun b => weightedOddSeries (c (a.succAbove b)) A)).prod)

/-- Coefficient extraction for the actual signed deletion power series. -/
theorem coeff_deletionSeries {q : ℕ} (e c : Fin (q + 1) → ℕ → R)
    (A : ℕ → M) (D : ℕ) :
    (deletionSeries e c A).coeff D =
      deletionDeficitCoefficient (D + 1) D D e c A := by
  simp only [deletionSeries, map_sum, PowerSeries.coeff_smul,
    coeff_scalar_mul_weightedProduct _ _ _ D (D + 1) (Nat.lt_succ_self D),
    Finset.smul_sum, smul_smul, deletionDeficitCoefficient]

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

/-- The selected determinant never vanishes in the actual exceptional
range, including the boundary cutoff `k=m<N`. -/
theorem det_eulerSelectorMatrix_ne_zero {q : ℕ} (b : ℤ) (m k : ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q = T.card) (hkm : k ≤ m) :
    (eulerSelectorMatrix (selector b k T) b (b - m) T hq).det ≠ 0 := by
  rw [det_eulerSelectorMatrix_eq_transferScalar b m k T hT hq]
  exact transferScalar_ne_zero m k T hkm

section RationalAlgebra

variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Module R M]

/-- Scalar extension of the selected matrix preserves its determinant. -/
theorem selectedMatrix_euler_det {q : ℕ} (p : Polynomial ℚ) (b ell : ℤ)
    (T : Finset ℕ) (hq : q = T.card) :
    (selectedMatrix T hq
      (fun a t => algebraMap ℚ R (eulerWeight p ell a.val t))
      (fun a t => algebraMap ℚ R (eulerWeight p b a.val t))).det =
      algebraMap ℚ R (eulerSelectorMatrix p b ell T hq).det := by
  rw [RingHom.map_det]
  congr 1
  ext a j
  induction j using Fin.cases with
  | zero => simp [selectedMatrix, eulerSelectorMatrix, selectedEigenvalues, eulerWeight]
  | succ j => simp [selectedMatrix, eulerSelectorMatrix, selectedEigenvalues, eulerWeight]

/-- ET-05--07 in explicit finite coefficients, over any rational algebra.
The coefficient is a single ordered exterior monomial, multiplied by the
Euler-selector determinant and the leading even coefficient. -/
theorem selector_deletion_coefficient {q : ℕ} (b ell : ℤ) (k L J : ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q = T.card)
    (hTL : T ⊆ Finset.range L) (v : ℕ → R) (A : ℕ → M) :
    deletionDeficitCoefficient (q := q) L J (∑ t ∈ T, t)
      (fun a j => v j * algebraMap ℚ R (eulerWeight (selector b k T) ell a.val j))
      (fun a t => algebraMap ℚ R (eulerWeight (selector b k T) b a.val t)) A =
    (v 0 * algebraMap ℚ R (eulerSelectorMatrix (selector b k T) b ell T hq).det) •
      ExteriorAlgebra.ιMulti R q (fun j => A (T.orderEmbOfFin hq.symm j)) := by
  rw [deletionDeficitCoefficient_eq_det k L J T hT hq hTL]
  · rw [selectedMatrix_det_even_mul, selectedMatrix_euler_det]
  · intro a t ht htT
    simp only [eulerWeight, eval_selector_eq_zero b k t T ht htT, mul_zero, map_zero]

/-- The selected coefficient with the determinant fully simplified. -/
theorem selector_deletion_coefficient_transferScalar {q : ℕ} (b : ℤ) (m k L J : ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q = T.card)
    (hTL : T ⊆ Finset.range L) (v : ℕ → R) (A : ℕ → M) :
    deletionDeficitCoefficient (q := q) L J (∑ t ∈ T, t)
      (fun a j => v j * algebraMap ℚ R
        (eulerWeight (selector b k T) (b - m) a.val j))
      (fun a t => algebraMap ℚ R (eulerWeight (selector b k T) b a.val t)) A =
    (v 0 * algebraMap ℚ R (transferScalar m k T)) •
      ExteriorAlgebra.ιMulti R q (fun j => A (T.orderEmbOfFin hq.symm j)) := by
  rw [selector_deletion_coefficient b (b - m) k L J T hT hq hTL,
    det_eulerSelectorMatrix_eq_transferScalar b m k T hT hq]

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

/-- Euler operations on the even series have the scalar coefficients used
in the finite coefficient theorem. -/
theorem iterate_evalEuler_scalarSeries (p : Polynomial ℚ) (b : ℤ) (a : ℕ)
    (v : ℕ → R) :
    ((CoefficientSeries.shiftedEuler b)^[a])
      (CoefficientSeries.evalEuler (p.map (algebraMap ℚ R)) b (scalarSeries (M := M) v)) =
      scalarSeries (M := M) (fun t => v t * algebraMap ℚ R (eulerWeight p b a t)) := by
  ext t
  rw [coeff_iterate_evalEuler_map]
  simp only [scalarSeries, PowerSeries.coeff_mk, Algebra.smul_def]
  rw [← map_mul, mul_comm]

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

/-- The formal Euler deletion expression agrees with the coefficient model. -/
theorem eulerDeletionSeries_eq_deletionSeries (q : ℕ) (p : Polynomial ℚ) (b ell : ℤ)
    (v : ℕ → R) (A : ℕ → M) :
    eulerDeletionSeries q p b ell (scalarSeries v) (weightedOddSeries (fun _ => 1) A) =
      deletionSeries (q := q)
        (fun a j => v j * algebraMap ℚ R (eulerWeight p ell a.val j))
        (fun a t => algebraMap ℚ R (eulerWeight p b a.val t)) A := by
  simp only [eulerDeletionSeries, deletionSeries,
    iterate_evalEuler_scalarSeries, iterate_evalEuler_weightedOddSeries]

/-- ET-05--07 for an actual power series: the selected coefficient is the
transfer scalar times the leading even coefficient and the selected
odd factors in increasing order. -/
theorem selector_deletionSeries_coeff {q : ℕ} (b : ℤ) (m k : ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q = T.card)
    (v : ℕ → R) (A : ℕ → M) :
    (deletionSeries (q := q)
      (fun a j => v j * algebraMap ℚ R
        (eulerWeight (selector b k T) (b - m) a.val j))
      (fun a t => algebraMap ℚ R (eulerWeight (selector b k T) b a.val t)) A).coeff
        (∑ t ∈ T, t) =
    (v 0 * algebraMap ℚ R (transferScalar m k T)) •
      ExteriorAlgebra.ιMulti R q (fun j => A (T.orderEmbOfFin hq.symm j)) := by
  rw [coeff_deletionSeries]
  apply selector_deletion_coefficient_transferScalar b m k _ _ T hT hq
  intro t ht
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (Finset.single_le_sum (fun i _ => Nat.zero_le i) ht)

/-- ET-05--07 directly for the polynomial in the Euler operator occurring
in the transfer identity. All factors and signs are before homology. -/
theorem eulerDeletionSeries_selector_coeff {q : ℕ} (b : ℤ) (m k : ℕ)
    (T : Finset ℕ) (hT : T ⊆ Finset.range k) (hq : q = T.card)
    (v : ℕ → R) (A : ℕ → M) :
    (eulerDeletionSeries q (selector b k T) b (b - m)
      (scalarSeries v) (weightedOddSeries (fun _ => 1) A)).coeff (∑ t ∈ T, t) =
    (v 0 * algebraMap ℚ R (transferScalar m k T)) •
      ExteriorAlgebra.ιMulti R q (fun j => A (T.orderEmbOfFin hq.symm j)) := by
  rw [eulerDeletionSeries_eq_deletionSeries]
  exact selector_deletionSeries_coeff b m k T hT hq v A

end RationalAlgebra

end TorusLinkHomology.CoefficientSelector
