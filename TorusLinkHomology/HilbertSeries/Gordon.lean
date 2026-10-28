import TorusLinkHomology.HilbertSeries.QSeries
import Mathlib.Order.Interval.Finset.Fin

/-! Finite sequence reindexing and algebraic identities for the explicit Gordon multisum. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

@[simp] theorem gordonCoefficient_zero_charge (N i : ℕ) :
    gordonCoefficient N i 0 = 1 := by
  classical
  let : Unique {m : Fin (N - 1) → Fin 1 // GordonAdmissible N 0 m} :=
    { default := ⟨fun _ => 0, by simp [GordonAdmissible, Antitone]⟩
      uniq := fun _ => Subtype.ext (Subsingleton.elim _ _) }
  unfold gordonCoefficient
  rw [Fintype.sum_unique]
  simp

theorem gordonCoefficient_rank_one_pos (i k : ℕ) (hk : 0 < k) :
    gordonCoefficient 1 i k = 0 := by
  classical
  have he : IsEmpty {m : Fin (1 - 1) → Fin (k + 1) // GordonAdmissible 1 k m} :=
    ⟨fun m => by have hm := m.property.2; simp at hm; omega⟩
  let := he
  simp [gordonCoefficient]

@[simp] theorem gordonCoefficient_rank_one (i k : ℕ) :
    gordonCoefficient 1 i k = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst k; exact gordonCoefficient_zero_charge _ _
  · exact gordonCoefficient_rank_one_pos i k (Nat.pos_of_ne_zero hk)

/-- Monotonicity bounds every entry of an admissible sequence by the charge
already spent on its prefix. -/
theorem GordonAdmissible.prefix_bound {N k : ℕ}
    {m : Fin (N - 1) → Fin (k + 1)} (hm : GordonAdmissible N k m)
    (j : Fin (N - 1)) : (j.val + 1) * (m j).val ≤ k := by
  calc
    (j.val + 1) * (m j).val = ∑ _l ∈ Finset.Iic j, (m j).val := by simp
    _ ≤ ∑ l ∈ Finset.Iic j, (m l).val :=
      Finset.sum_le_sum (fun l hl => hm.1 (Finset.mem_Iic.mp hl))
    _ ≤ ∑ l : Fin (N - 1), (m l).val :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = k := hm.2

theorem GordonAdmissible.entry_eq_zero {N k : ℕ}
    {m : Fin (N - 1) → Fin (k + 1)} (hm : GordonAdmissible N k m)
    (j : Fin (N - 1)) (hj : k < j.val + 1) : (m j).val = 0 := by
  have hb := hm.prefix_bound j
  by_contra hn
  have hl : j.val + 1 ≤ (j.val + 1) * (m j).val :=
    Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn)
  omega

/-- The zero branch of the Gordon recurrence follows term by term when the
charge is too small to reach the removed entry. -/
theorem gordonCoefficient_eq_previous_of_lt (N i k : ℕ) (hi : 1 ≤ i)
    (hiN : i + 1 ≤ N) (hk : k < i) :
    gordonCoefficient N (i + 1) k = gordonCoefficient N i k := by
  classical
  unfold gordonCoefficient
  apply Finset.sum_congr rfl
  intro m _
  dsimp only
  have hidx : i - 1 < N - 1 := by omega
  have hz := m.property.entry_eq_zero ⟨i - 1, hidx⟩ (by simp; omega)
  have hs : (∑ j ∈ Finset.Ico (i - 1) (N - 1),
      if hj : j < N - 1 then (m.val ⟨j, hj⟩).val else 0) =
      ∑ j ∈ Finset.Ico i (N - 1),
        if hj : j < N - 1 then (m.val ⟨j, hj⟩).val else 0 := by
    rw [Finset.sum_eq_sum_Ico_succ_bot hidx]
    simp [hidx, hz, Nat.sub_add_cancel hi]
  simp only [Nat.add_sub_cancel, hs]

/-- The first Gordon recurrence endpoint is a direct shift by the charge.
No partition interpretation is needed. -/
theorem gordonCoefficient_first (N k : ℕ) :
    gordonCoefficient N 1 k = (MvPowerSeries.X 1 : ChargeSeries) ^ k *
      gordonCoefficient N N k := by
  classical
  unfold gordonCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  dsimp only
  have hs : (∑ j ∈ Finset.range (N - 1),
      if hj : j < N - 1 then (m.val ⟨j, hj⟩).val else 0) = k := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa using m.property.2
  simp only [Nat.sub_self, Nat.Ico_zero_eq_range, Finset.Ico_self,
    Finset.sum_empty, add_zero, hs, pow_add]
  ring

@[simp] theorem fermionicCoefficient_rank_one (k : ℕ) :
    fermionicCoefficient 1 k = if k = 0 then 1 else 0 := by
  simp only [fermionicCoefficient, Nat.sub_self, not_lt_zero, ↓reduceIte,
    gordonCoefficient_rank_one, Finset.Ico_self, Finset.sum_empty, mul_zero, add_zero]
  split_ifs with hk
  · subst k; simp
  · simp

@[simp] theorem fermionicCoefficient_zero_charge (N : ℕ) (hN : 0 < N) :
    fermionicCoefficient N 0 = 1 := by
  by_cases h : N = 1
  · subst N; simp
  · have hN' : 0 < N - 1 := by omega
    simp [fermionicCoefficient, hN']

/-- Rank two has one admissible sequence at each charge. -/
theorem gordonCoefficient_rank_two (k : ℕ) :
    gordonCoefficient 2 2 k = (MvPowerSeries.X 1 : ChargeSeries) ^ (k * (k - 1)) *
      (qPochhammer (MvPowerSeries.X 1 : ChargeSeries) (MvPowerSeries.X 1) k)⁻¹ := by
  classical
  let : Unique {m : Fin (2 - 1) → Fin (k + 1) // GordonAdmissible 2 k m} :=
    { default := ⟨fun _ => ⟨k, Nat.lt_succ_self k⟩,
        by simp [GordonAdmissible, Antitone]⟩
      uniq := fun m => by
        apply Subtype.ext
        funext j
        fin_cases j
        apply Fin.ext
        simpa using m.property.2 }
  unfold gordonCoefficient
  rw [Fintype.sum_unique]
  simp
  rfl

/-- The positive-charge recurrence at the other rank-two endpoint. -/
theorem gordonCoefficient_rank_two_recurrence (k : ℕ) :
    gordonCoefficient 2 2 (k + 1) - gordonCoefficient 2 1 (k + 1) =
      (MvPowerSeries.X 1 : ChargeSeries) ^ k * gordonCoefficient 2 1 k := by
  rw [gordonCoefficient_first, gordonCoefficient_first,
    gordonCoefficient_rank_two, gordonCoefficient_rank_two]
  let v : ChargeSeries := MvPowerSeries.X 1
  have he : (k + 1) * (k + 1 - 1) = k + k + k * (k - 1) := by
    cases k
    · simp
    · simp; ring
  calc
    v ^ ((k + 1) * (k + 1 - 1)) * (qPochhammer v v (k + 1))⁻¹ -
        v ^ (k + 1) * (v ^ ((k + 1) * (k + 1 - 1)) * (qPochhammer v v (k + 1))⁻¹) =
      v ^ ((k + 1) * (k + 1 - 1)) *
        ((1 - v ^ (k + 1)) * (qPochhammer v v (k + 1))⁻¹) := by ring
    _ = v ^ ((k + 1) * (k + 1 - 1)) * (qPochhammer v v k)⁻¹ := by
      rw [qPochhammer_inv_step v (by simp [v])]
    _ = _ := by rw [he, pow_add, pow_add]; ring

/-- Decreasing sequences with a fixed charge, without an artificial entry bound.
The charge supplies the bound needed for finiteness. -/
abbrev GordonSequence (r k : ℕ) :=
  {m : Fin r → ℕ // Antitone m ∧ (∑ j : Fin r, m j) = k}

namespace GordonSequence

theorem entry_le {r k : ℕ} (m : GordonSequence r k) (j : Fin r) : m.val j ≤ k := by
  calc
    m.val j ≤ ∑ l : Fin r, m.val l :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = k := m.property.2

/-- Removing the bounds does not change the existing explicit indexing type. -/
def boundedEquiv (r k : ℕ) :
    GordonSequence r k ≃ {m : Fin r → Fin (k + 1) // GordonAdmissible (r + 1) k m} where
  toFun m := ⟨fun j => ⟨m.val j, Nat.lt_succ_of_le (m.entry_le j)⟩, m.property⟩
  invFun m := ⟨fun j => (m.val j).val, m.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (r k : ℕ) : Fintype (GordonSequence r k) := by
  classical
  exact Fintype.ofEquiv {m : Fin r → Fin (k + 1) // GordonAdmissible (r + 1) k m}
    (boundedEquiv r k).symm

/-- Subtract the last entry from every preceding entry. -/
def stripValues {r k : ℕ} (m : GordonSequence (r + 1) k) : Fin r → ℕ :=
  fun j => m.val j.castSucc - m.val (Fin.last r)

theorem last_le {r k : ℕ} (m : GordonSequence (r + 1) k) (j : Fin r) :
    m.val (Fin.last r) ≤ m.val j.castSucc :=
  m.property.1 (Fin.le_last _)

theorem strip_charge {r k : ℕ} (m : GordonSequence (r + 1) k) :
    (∑ j : Fin r, stripValues m j) + (r + 1) * m.val (Fin.last r) = k := by
  calc
    _ = (∑ j : Fin r, (stripValues m j + m.val (Fin.last r))) + m.val (Fin.last r) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      ring
    _ = (∑ j : Fin r, m.val j.castSucc) + m.val (Fin.last r) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact Nat.sub_add_cancel (m.last_le j)
    _ = k := by rw [← Fin.sum_univ_castSucc]; exact m.property.2

theorem last_charge_bound {r k : ℕ} (m : GordonSequence (r + 1) k) :
    (r + 1) * m.val (Fin.last r) ≤ k := by
  have he := m.strip_charge
  omega

/-- The lower-rank sequence after splitting off the last entry. -/
def stripLast {r k : ℕ} (m : GordonSequence (r + 1) k) :
    GordonSequence r (k - (r + 1) * m.val (Fin.last r)) := by
  refine ⟨stripValues m, ?_, ?_⟩
  · intro i j hij
    exact Nat.sub_le_sub_right (m.property.1 (Fin.castSucc_le_castSucc_iff.mpr hij)) _
  · have he := m.strip_charge
    omega

/-- Add a constant to every entry and append that constant as the last entry. -/
def appendLast (r k t : ℕ) (m : GordonSequence r k) :
    GordonSequence (r + 1) (k + (r + 1) * t) := by
  refine ⟨Fin.lastCases t (fun j => m.val j + t), ?_, ?_⟩
  · intro i j
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · intro hij
      have hj : j = Fin.last r := le_antisymm (Fin.le_last _) hij
      subst j
      exact le_refl _
    · refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro _; simp
      · intro hij
        simpa using Nat.add_le_add_right (m.property.1
          (Fin.castSucc_le_castSucc_iff.mp hij)) t
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, m.property.2]
    ring

/-- The finite index set for the last entry in the rank-reduction sum. -/
abbrev LastIndex (r k : ℕ) := {t : Fin (k + 1) // (r + 1) * t.val ≤ k}

/-- Splitting off the last entry is an actual equivalence of the finite
multisum indices. In particular this introduces no partition identity. -/
def splitLastEquiv (r k : ℕ) : GordonSequence (r + 1) k ≃
    Σ t : LastIndex r k, GordonSequence r (k - (r + 1) * t.val.val) where
  toFun m := ⟨⟨⟨m.val (Fin.last r), Nat.lt_succ_of_le (m.entry_le _)⟩,
      m.last_charge_bound⟩, m.stripLast⟩
  invFun m := ⟨(appendLast r _ m.1.val.val m.2).val,
    (appendLast r _ m.1.val.val m.2).property.1,
    (appendLast r _ m.1.val.val m.2).property.2.trans (Nat.sub_add_cancel m.1.property)⟩
  left_inv m := by
    apply Subtype.ext
    funext j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [appendLast]
    · simpa [appendLast, stripLast, stripValues] using Nat.sub_add_cancel (m.last_le j')
  right_inv m := by
    rcases m with ⟨⟨⟨t, ht⟩, htk⟩, m⟩
    apply Sigma.ext
    · apply Subtype.ext
      apply Fin.ext
      simp [appendLast]
    · apply (Subtype.heq_iff_coe_eq ?_).mpr
      · funext j
        simp [stripLast, stripValues, appendLast]
      · intro f
        simp [appendLast]

/-- Zero extension of a finite decreasing sequence. -/
def value {r k : ℕ} (m : GordonSequence r k) (j : ℕ) : ℕ :=
  if hj : j < r then m.val ⟨j, hj⟩ else 0

@[simp] theorem value_fin {r k : ℕ} (m : GordonSequence r k) (j : Fin r) :
    m.value j.val = m.val j := by simp [value]

@[simp] theorem value_ge {r k : ℕ} (m : GordonSequence r k) {j : ℕ} (hj : r ≤ j) :
    m.value j = 0 := by simp [value, Nat.not_lt.mpr hj]

/-- The summand of the existing Gordon multisum in unbounded sequence coordinates. -/
def summand {r k : ℕ} (m : GordonSequence r k) (i : ℕ) : ChargeSeries :=
  let v : ChargeSeries := MvPowerSeries.X 1
  v ^ ((∑ j : Fin r, m.val j * (m.val j - 1)) +
    ∑ j ∈ Finset.Ico (i - 1) r, m.value j) *
    (∏ j : Fin r, qPochhammer v v (m.val j - m.value (j.val + 1)))⁻¹

@[simp] theorem appendLast_value {r k : ℕ} (m : GordonSequence r k) (t j : ℕ)
    (hj : j ≤ r) : (appendLast r k t m).value j = m.value j + t := by
  by_cases hlt : j < r
  · have hj' : j < r + 1 := by omega
    change (if h : j < r + 1 then Fin.lastCases t (fun l => m.val l + t) ⟨j, h⟩ else 0) = _
    rw [dif_pos hj']
    change (Fin.lastCases t (fun l => m.val l + t) : Fin (r + 1) → ℕ) (Fin.castSucc ⟨j, hlt⟩) = _
    exact (Fin.lastCases_castSucc (motive := fun _ : Fin (r + 1) => ℕ)
      (last := t) (cast := fun l => m.val l + t) ⟨j, hlt⟩).trans (by simp [value, hlt])
  · have he : j = r := by omega
    subst j
    change (if h : r < r + 1 then Fin.lastCases t (fun l => m.val l + t) ⟨r, h⟩ else 0) = _
    rw [dif_pos (Nat.lt_succ_self r)]
    change (Fin.lastCases t (fun l => m.val l + t) : Fin (r + 1) → ℕ) (Fin.last r) = _
    simp

private theorem quadratic_add (a b : ℕ) :
    (a + b) * (a + b - 1) = a * (a - 1) + 2 * b * a + b * (b - 1) := by
  cases a with
  | zero => simp
  | succ a =>
    cases b with
    | zero => simp
    | succ b => simp; ring

/-- The quadratic exponent after splitting off the last entry. -/
theorem appendLast_quadratic {r k : ℕ} (m : GordonSequence r k) (t : ℕ) :
    (∑ j : Fin (r + 1), (appendLast r k t m).val j * ((appendLast r k t m).val j - 1)) =
      (∑ j : Fin r, m.val j * (m.val j - 1)) + 2 * t * k + (r + 1) * (t * (t - 1)) := by
  rw [Fin.sum_univ_castSucc]
  simp only [appendLast, Fin.lastCases_castSucc, Fin.lastCases_last, quadratic_add,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum, m.property.2]
  ring

/-- The linear exponent after splitting off the last entry. -/
theorem appendLast_suffix {r k : ℕ} (m : GordonSequence r k) (t i : ℕ) (hi : 1 ≤ i) :
    (∑ j ∈ Finset.Ico (i - 1) (r + 1), (appendLast r k t m).value j) =
      (∑ j ∈ Finset.Ico (i - 1) r, m.value j) + (r + 2 - i) * t := by
  by_cases hir : i - 1 ≤ r
  · rw [Finset.sum_Ico_succ_top hir]
    rw [appendLast_value m t r (le_refl _)]
    have he : (∑ j ∈ Finset.Ico (i - 1) r, (appendLast r k t m).value j) =
        ∑ j ∈ Finset.Ico (i - 1) r, (m.value j + t) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact appendLast_value m t j (by have := (Finset.mem_Ico.mp hj).2; omega)
    rw [he]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
      nsmul_eq_mul, Nat.cast_id, value_ge m (le_refl r), zero_add]
    have hcount : r + 2 - i = (r - (i - 1)) + 1 := by omega
    rw [hcount]
    ring
  · have h1 : r + 1 ≤ i - 1 := by omega
    have h2 : r + 2 - i = 0 := by omega
    simp [Finset.Ico_eq_empty_of_le h1,
      Finset.Ico_eq_empty_of_le (show r ≤ i - 1 by omega), h2]

/-- The denominator factors split into the lower-rank denominator and `(v;v)_t`. -/
theorem appendLast_denominator {r k : ℕ} (m : GordonSequence r k) (t : ℕ)
    (v : ChargeSeries) :
    (∏ j : Fin (r + 1), qPochhammer v v
      ((appendLast r k t m).val j - (appendLast r k t m).value (j.val + 1))) =
      (∏ j : Fin r, qPochhammer v v (m.val j - m.value (j.val + 1))) * qPochhammer v v t := by
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    simp only [Fin.val_castSucc]
    rw [appendLast_value m t (j.val + 1) (by have := j.isLt; omega)]
    simp [appendLast, Nat.add_sub_add_right]
  · simp [appendLast]

/-- Rank reduction at the level of each summand, including every exponent. -/
theorem appendLast_summand {r k : ℕ} (m : GordonSequence r k) (t i : ℕ) (hi : 1 ≤ i) :
    (appendLast r k t m).summand i =
      (MvPowerSeries.X 1 : ChargeSeries) ^ (2 * t * k + (r + 1) * (t * (t - 1)) + (r + 2 - i) * t) *
        (qPochhammer (MvPowerSeries.X 1 : ChargeSeries) (MvPowerSeries.X 1) t)⁻¹ * m.summand i := by
  dsimp only [summand]
  rw [appendLast_quadratic, appendLast_suffix m t i hi, appendLast_denominator,
    MvPowerSeries.mul_inv_rev]
  simp only [pow_add]
  ring

end GordonSequence

/-- Reindexing the existing explicit multisum by unbounded sequences. -/
theorem gordonCoefficient_eq_sum_sequences (r i k : ℕ) :
    gordonCoefficient (r + 1) i k = ∑ m : GordonSequence r k, m.summand i := by
  classical
  unfold gordonCoefficient
  dsimp only
  symm
  refine Fintype.sum_equiv (GordonSequence.boundedEquiv r k) _ _ ?_
  intro m
  change m.summand i = (MvPowerSeries.X 1 : ChargeSeries) ^
    ((∑ j ∈ Finset.range r, m.value j * (m.value j - 1)) +
      ∑ j ∈ Finset.Ico (i - 1) r, m.value j) *
      (∏ j ∈ Finset.range r, qPochhammer (MvPowerSeries.X 1 : ChargeSeries)
        (MvPowerSeries.X 1) (m.value j - m.value (j + 1)))⁻¹
  dsimp only [GordonSequence.summand]
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.prod_univ_eq_prod_range]
  simp only [GordonSequence.value_fin]

/-- Rank reduction of the existing explicit multisum, obtained by splitting
its last sequence entry. Every sum here is finite. -/
theorem gordonCoefficient_rank_reduction (r i k : ℕ) (hi : 1 ≤ i) :
    gordonCoefficient (r + 2) i k =
      ∑ t : GordonSequence.LastIndex r k,
        (MvPowerSeries.X 1 : ChargeSeries) ^
          (2 * t.val.val * (k - (r + 1) * t.val.val) +
            (r + 1) * (t.val.val * (t.val.val - 1)) + (r + 2 - i) * t.val.val) *
          (qPochhammer (MvPowerSeries.X 1 : ChargeSeries) (MvPowerSeries.X 1) t.val.val)⁻¹ *
          gordonCoefficient (r + 1) i (k - (r + 1) * t.val.val) := by
  classical
  rw [gordonCoefficient_eq_sum_sequences (r + 1)]
  rw [← Equiv.sum_comp (GordonSequence.splitLastEquiv r k).symm
    (fun m : GordonSequence (r + 1) k => m.summand i)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  change (∑ m : GordonSequence r (k - (r + 1) * t.val.val),
    (GordonSequence.appendLast r _ t.val.val m).summand i) = _
  simp_rw [GordonSequence.appendLast_summand _ _ _ hi]
  rw [← Finset.mul_sum, ← gordonCoefficient_eq_sum_sequences]

/-- Indices beyond the rank have the same empty linear-exponent suffix. -/
theorem gordonCoefficient_index_ge (N i k : ℕ) (hi : N ≤ i) :
    gordonCoefficient N i k = gordonCoefficient N N k := by
  classical
  unfold gordonCoefficient
  apply Finset.sum_congr rfl
  intro m _
  simp [Finset.Ico_eq_empty_of_le (show N - 1 ≤ i - 1 by omega)]

namespace GordonSequence

private theorem lastIndex_le {r k : ℕ} (t : LastIndex r k) : t.val.val ≤ k := by
  have h := t.property
  nlinarith

/-- Reindex a positive last entry by subtracting one, with the zero entry
represented separately. This is the finite shift used in telescoping. -/
def lastIndexOptionEquiv (r k : ℕ) :
    Option (LastIndex r k) ≃ LastIndex r (k + (r + 1)) where
  toFun
    | none => ⟨⟨0, by omega⟩, by simp⟩
    | some t => ⟨⟨t.val.val + 1, by have := lastIndex_le t; omega⟩, by
        have ht := t.property
        simpa [Nat.mul_add] using Nat.add_le_add_right ht (r + 1)⟩
  invFun t := if ht : t.val.val = 0 then none else some ⟨⟨t.val.val - 1, by
      have hmul : (r + 1) * (t.val.val - 1) ≤ k := by
        have hh := t.property
        have he : (r + 1) * t.val.val = (r + 1) * (t.val.val - 1) + (r + 1) := by
          rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ t.val.val)]
        omega
      have hl : t.val.val - 1 ≤ (r + 1) * (t.val.val - 1) := by nlinarith
      omega⟩, by
      change (r + 1) * (t.val.val - 1) ≤ k
      have hh := t.property
      have he : (r + 1) * t.val.val = (r + 1) * (t.val.val - 1) + (r + 1) := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ t.val.val)]
      omega⟩
  left_inv t := by
    cases t with
    | none => simp
    | some t => simp
  right_inv t := by
    dsimp only
    split_ifs with ht
    · apply Subtype.ext; apply Fin.ext; exact ht.symm
    · apply Subtype.ext; apply Fin.ext
      exact Nat.sub_add_cancel (by omega)

end GordonSequence

/-- The finite rank-reduction summand, including its lower-rank coefficient. -/
def gordonRankTerm (r i k t : ℕ) : ChargeSeries :=
  (MvPowerSeries.X 1 : ChargeSeries) ^
    (2 * t * (k - (r + 1) * t) + (r + 1) * (t * (t - 1)) + (r + 2 - i) * t) *
    (qPochhammer (MvPowerSeries.X 1 : ChargeSeries) (MvPowerSeries.X 1) t)⁻¹ *
    gordonCoefficient (r + 1) i (k - (r + 1) * t)

theorem gordonCoefficient_eq_sum_rankTerm (r i k : ℕ) (hi : 1 ≤ i) :
    gordonCoefficient (r + 2) i k =
      ∑ t : GordonSequence.LastIndex r k, gordonRankTerm r i k t.val.val :=
  gordonCoefficient_rank_reduction r i k hi

theorem gordonRankTerm_top_zero (r k : ℕ) :
    gordonRankTerm r (r + 2) k 0 - gordonRankTerm r (r + 1) k 0 = 0 := by
  simp [gordonRankTerm, gordonCoefficient_index_ge (r + 1) (r + 2) k (by omega)]

/-- Denominator cancellation and the shift of the last entry at the top endpoint. -/
theorem gordonRankTerm_top_succ (r k t : ℕ) (ht : (r + 1) * t ≤ k) :
    gordonRankTerm r (r + 2) (k + (r + 1)) (t + 1) -
      gordonRankTerm r (r + 1) (k + (r + 1)) (t + 1) =
      (MvPowerSeries.X 1 : ChargeSeries) ^ (2 * k) * gordonRankTerm r (r + 2) k t := by
  have hc : k + (r + 1) - (r + 1) * (t + 1) = k - (r + 1) * t := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_sub_add_right]
  have htq : t * (t - 1) + t = t * t := by
    cases t
    · simp
    · simp; ring
  have hkc := Nat.sub_add_cancel ht
  have he : 2 * (t + 1) * (k - (r + 1) * t) + (r + 1) * ((t + 1) * t) =
      2 * k + (2 * t * (k - (r + 1) * t) + (r + 1) * (t * (t - 1))) := by
    nlinarith
  dsimp only [gordonRankTerm]
  simp only [hc, Nat.add_sub_cancel, Nat.sub_self, zero_mul, add_zero]
  rw [gordonCoefficient_index_ge (r + 1) (r + 2) _ (by omega)]
  simp only [show r + 2 - (r + 1) = 1 by omega, one_mul]
  let v : ChargeSeries := MvPowerSeries.X 1
  let e := 2 * (t + 1) * (k - (r + 1) * t) + (r + 1) * ((t + 1) * t)
  let G := gordonCoefficient (r + 1) (r + 1) (k - (r + 1) * t)
  change v ^ e * (qPochhammer v v (t + 1))⁻¹ * G -
    v ^ (e + (t + 1)) * (qPochhammer v v (t + 1))⁻¹ * G = _
  calc
    _ = v ^ e * ((1 - v ^ (t + 1)) * (qPochhammer v v (t + 1))⁻¹) * G := by
      rw [pow_add]; ring
    _ = v ^ e * (qPochhammer v v t)⁻¹ * G := by
      rw [qPochhammer_inv_step v (by simp [v])]
    _ = _ := by
      dsimp only [e]
      rw [he, pow_add]
      ring

/-- The positive-charge Gordon recurrence at i=N for every rank N≥2. -/
theorem gordonCoefficient_top_recurrence (r k : ℕ) :
    gordonCoefficient (r + 2) (r + 2) (k + (r + 1)) -
      gordonCoefficient (r + 2) (r + 1) (k + (r + 1)) =
      (MvPowerSeries.X 1 : ChargeSeries) ^ k * gordonCoefficient (r + 2) 1 k := by
  classical
  rw [gordonCoefficient_eq_sum_rankTerm r (r + 2) _ (by omega),
    gordonCoefficient_eq_sum_rankTerm r (r + 1) _ (by omega), ← Finset.sum_sub_distrib]
  rw [← Equiv.sum_comp (GordonSequence.lastIndexOptionEquiv r k)
    (fun t : GordonSequence.LastIndex r (k + (r + 1)) =>
      gordonRankTerm r (r + 2) (k + (r + 1)) t.val.val -
        gordonRankTerm r (r + 1) (k + (r + 1)) t.val.val)]
  rw [Fintype.sum_option]
  change (gordonRankTerm r (r + 2) (k + (r + 1)) 0 -
    gordonRankTerm r (r + 1) (k + (r + 1)) 0) +
      (∑ t : GordonSequence.LastIndex r k,
        (gordonRankTerm r (r + 2) (k + (r + 1)) (t.val.val + 1) -
          gordonRankTerm r (r + 1) (k + (r + 1)) (t.val.val + 1))) = _
  rw [gordonRankTerm_top_zero, zero_add]
  have hs (t : GordonSequence.LastIndex r k) := gordonRankTerm_top_succ r k t.val.val t.property
  simp_rw [hs]
  rw [← Finset.mul_sum, ← gordonCoefficient_eq_sum_rankTerm r (r + 2) k (by omega),
    gordonCoefficient_first]
  rw [show 2 * k = k + k by omega, pow_add]
  ring

/-- The scalar factor in a rank-reduction summand. -/
def gordonRankFactor (r i k t : ℕ) : ChargeSeries :=
  (MvPowerSeries.X 1 : ChargeSeries) ^
    (2 * t * (k - (r + 1) * t) + (r + 1) * (t * (t - 1)) + (r + 2 - i) * t) *
    (qPochhammer (MvPowerSeries.X 1 : ChargeSeries) (MvPowerSeries.X 1) t)⁻¹

theorem gordonRankFactor_previous (r i k t : ℕ) (hi : 2 ≤ i) (hiN : i ≤ r + 2) :
    gordonRankFactor r (i - 1) k t =
      (MvPowerSeries.X 1 : ChargeSeries) ^ t * gordonRankFactor r i k t := by
  have he : r + 2 - (i - 1) = (r + 2 - i) + 1 := by omega
  unfold gordonRankFactor
  rw [he, Nat.add_mul, one_mul]
  simp only [pow_add]
  ring

/-- The first lower-rank recurrence term has exactly the reflected rank factor. -/
theorem gordonRankFactor_reflect (r i k t : ℕ) (hi : 2 ≤ i) (hiN : i ≤ r + 1)
    (ht : (r + 1) * t ≤ k) :
    gordonRankFactor r i (k + (i - 1)) t *
        (MvPowerSeries.X 1 : ChargeSeries) ^ (k - (r + 1) * t) =
      (MvPowerSeries.X 1 : ChargeSeries) ^ k * gordonRankFactor r (r + 3 - i) k t := by
  have hc : k + (i - 1) - (r + 1) * t = (k - (r + 1) * t) + (i - 1) := by omega
  have hj : r + 2 - (r + 3 - i) = i - 1 := by omega
  have hidx : r + 2 - i + (i - 1) = r + 1 := by omega
  have hkc := Nat.sub_add_cancel ht
  have he : (2 * t * (k + (i - 1) - (r + 1) * t) +
      (r + 1) * (t * (t - 1)) + (r + 2 - i) * t) + (k - (r + 1) * t) =
      k + (2 * t * (k - (r + 1) * t) + (r + 1) * (t * (t - 1)) + (i - 1) * t) := by
    rw [hc]
    nlinarith [congrArg (fun x => x * t) hidx]
  unfold gordonRankFactor
  rw [hj]
  calc
    _ = (MvPowerSeries.X 1 : ChargeSeries) ^
        ((2 * t * (k + (i - 1) - (r + 1) * t) + (r + 1) * (t * (t - 1)) +
          (r + 2 - i) * t) + (k - (r + 1) * t)) *
        (qPochhammer (MvPowerSeries.X 1 : ChargeSeries) (MvPowerSeries.X 1) t)⁻¹ := by
      rw [pow_add]; ring
    _ = _ := by rw [he, pow_add]; ring

/-- The second reflected recurrence term is the next telescoping correction.
The factor `(1-v^(t+1))` cancels its Pochhammer denominator. -/
theorem gordonRankFactor_correction_succ (r i k t : ℕ)
    (hi : 2 ≤ i) (hiN : i ≤ r + 1) (ht : (r + 1) * t ≤ k)
    (hs : (r + 1) * (t + 1) ≤ k + (i - 1)) :
    gordonRankFactor r i (k + (i - 1)) (t + 1) *
        (1 - (MvPowerSeries.X 1 : ChargeSeries) ^ (t + 1)) =
      (MvPowerSeries.X 1 : ChargeSeries) ^ k * gordonRankFactor r (r + 3 - i) k t *
        (MvPowerSeries.X 1 : ChargeSeries) ^ (k - (r + 1) * t - (r + 2 - i)) := by
  have hj : r + 2 - (r + 3 - i) = i - 1 := by omega
  have hidx : r + 2 - i + (i - 1) = r + 1 := by omega
  have hkc := Nat.sub_add_cancel ht
  have hs' : r + 2 - i ≤ k - (r + 1) * t := by
    rw [Nat.mul_add, Nat.mul_one] at hs
    omega
  have hqc := Nat.sub_add_cancel hs'
  have hc : k + (i - 1) - (r + 1) * (t + 1) = k - (r + 1) * t - (r + 2 - i) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have htq : t * (t - 1) + t = t * t := by
    cases t
    · simp
    · simp; ring
  have he : 2 * (t + 1) * (k + (i - 1) - (r + 1) * (t + 1)) +
      (r + 1) * ((t + 1) * t) + (r + 2 - i) * (t + 1) =
      (k + (2 * t * (k - (r + 1) * t) + (r + 1) * (t * (t - 1)) + (i - 1) * t)) +
        (k - (r + 1) * t - (r + 2 - i)) := by
    rw [hc]
    nlinarith [congrArg (fun x => 2 * (t + 1) * x) hqc,
      congrArg (fun x => x * t) hidx, congrArg (fun x => (r + 1) * x) htq]
  unfold gordonRankFactor
  simp only [Nat.add_sub_cancel, hj]
  let v : ChargeSeries := MvPowerSeries.X 1
  calc
    _ = v ^ (2 * (t + 1) * (k + (i - 1) - (r + 1) * (t + 1)) +
        (r + 1) * ((t + 1) * t) + (r + 2 - i) * (t + 1)) *
        ((1 - v ^ (t + 1)) * (qPochhammer v v (t + 1))⁻¹) := by ring
    _ = _ := by
      rw [qPochhammer_inv_step v (by simp [v]), he, pow_add, pow_add]
      ring

/-- Extend a rank-reduction summand by zero outside its charge support. -/
def gordonRankTermSupported (r i k t : ℕ) : ChargeSeries :=
  if (r + 1) * t ≤ k then gordonRankTerm r i k t else 0

/-- The finite telescoping correction in the interior Gordon recurrence. -/
def gordonRankCorrection (r i k t : ℕ) : ChargeSeries :=
  if (r + 1) * t ≤ k then
    gordonRankFactor r i k t * (1 - (MvPowerSeries.X 1 : ChargeSeries) ^ t) *
      gordonCoefficient (r + 1) (i - 1) (k - (r + 1) * t)
  else 0

/-- Pointwise telescoping reduces the interior recurrence to the already proved
recurrences at the preceding rank. -/
theorem gordonRankTerm_telescoping (r i k t : ℕ) (hi : 2 ≤ i) (hiN : i ≤ r + 1)
    (hrec : ∀ j q, 2 ≤ j → j ≤ r + 1 →
      gordonCoefficient (r + 1) j q - gordonCoefficient (r + 1) (j - 1) q =
        if j - 1 ≤ q then (MvPowerSeries.X 1 : ChargeSeries) ^ (q - (j - 1)) *
          gordonCoefficient (r + 1) (r + 1 - j + 1) (q - (j - 1)) else 0) :
    gordonRankTermSupported r i (k + (i - 1)) t -
      gordonRankTermSupported r (i - 1) (k + (i - 1)) t =
      (MvPowerSeries.X 1 : ChargeSeries) ^ k * gordonRankTermSupported r (r + 3 - i) k t +
        gordonRankCorrection r i (k + (i - 1)) t -
        gordonRankCorrection r i (k + (i - 1)) (t + 1) := by
  let v : ChargeSeries := MvPowerSeries.X 1
  by_cases hKt : (r + 1) * t ≤ k + (i - 1)
  · have hdiff : gordonRankTerm r i (k + (i - 1)) t -
        gordonRankTerm r (i - 1) (k + (i - 1)) t =
      gordonRankFactor r i (k + (i - 1)) t *
        (gordonCoefficient (r + 1) i (k + (i - 1) - (r + 1) * t) -
          gordonCoefficient (r + 1) (i - 1) (k + (i - 1) - (r + 1) * t)) +
      gordonRankCorrection r i (k + (i - 1)) t := by
      change gordonRankFactor r i _ t * _ - gordonRankFactor r (i - 1) _ t * _ = _
      rw [gordonRankFactor_previous r i _ t hi (by omega)]
      simp only [gordonRankCorrection, if_pos hKt]
      ring
    simp only [gordonRankTermSupported, if_pos hKt]
    rw [hdiff]
    by_cases hkt : (r + 1) * t ≤ k
    · rw [if_pos hkt]
      have hp : i - 1 ≤ k + (i - 1) - (r + 1) * t := by omega
      have hq : k + (i - 1) - (r + 1) * t - (i - 1) = k - (r + 1) * t := by omega
      have hreflect : r + 1 - i + 1 = r + 2 - i := by omega
      rw [hrec i _ hi hiN, if_pos hp, hq, hreflect, ← mul_assoc,
        gordonRankFactor_reflect r i k t hi hiN hkt]
      have hjlo : 2 ≤ r + 3 - i := by omega
      have hjhi : r + 3 - i ≤ r + 1 := by omega
      have hjprev : r + 3 - i - 1 = r + 2 - i := by omega
      have hjreflect : r + 1 - (r + 3 - i) + 1 = i - 1 := by omega
      have hjrec := hrec (r + 3 - i) (k - (r + 1) * t) hjlo hjhi
      rw [hjprev, hjreflect] at hjrec
      by_cases hs : (r + 1) * (t + 1) ≤ k + (i - 1)
      · have hle : r + 2 - i ≤ k - (r + 1) * t := by
          rw [Nat.mul_add, Nat.mul_one] at hs
          omega
        rw [if_pos hle] at hjrec
        have hc : k + (i - 1) - (r + 1) * (t + 1) =
            k - (r + 1) * t - (r + 2 - i) := by
          rw [Nat.mul_add, Nat.mul_one]
          omega
        simp only [gordonRankCorrection, if_pos hs]
        rw [gordonRankFactor_correction_succ r i k t hi hiN hkt hs, hc]
        change _ = v ^ k * (gordonRankFactor r (r + 3 - i) k t * _) + _ - _
        linear_combination -(v ^ k * gordonRankFactor r (r + 3 - i) k t) * hjrec
      · have hnot : ¬ r + 2 - i ≤ k - (r + 1) * t := by
          rw [Nat.mul_add, Nat.mul_one] at hs
          omega
        rw [if_neg hnot] at hjrec
        have he := sub_eq_zero.mp hjrec
        simp only [gordonRankCorrection, if_neg hs, sub_zero]
        change _ = v ^ k * (gordonRankFactor r (r + 3 - i) k t * _) + _
        rw [he]
        ring
    · have hp : ¬ i - 1 ≤ k + (i - 1) - (r + 1) * t := by omega
      have hs : ¬ (r + 1) * (t + 1) ≤ k + (i - 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [if_neg hkt, hrec i _ hi hiN, if_neg hp, mul_zero, zero_add]
      simp only [gordonRankCorrection, if_neg hs, mul_zero, zero_add, sub_zero]
  · have hkt : ¬ (r + 1) * t ≤ k := by omega
    have hs : ¬ (r + 1) * (t + 1) ≤ k + (i - 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    simp [gordonRankTermSupported, gordonRankCorrection, hKt, hkt, hs]

theorem gordonCoefficient_eq_sum_supported (r i k : ℕ) (hi : 1 ≤ i) :
    gordonCoefficient (r + 2) i k =
      ∑ t ∈ Finset.range (k + 1), gordonRankTermSupported r i k t := by
  classical
  rw [gordonCoefficient_eq_sum_rankTerm r i k hi]
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun t : Fin (k + 1) => (r + 1) * t.val ≤ k))
    (by intro t; simp) (fun t : Fin (k + 1) => gordonRankTerm r i k t.val)]
  rw [Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range (gordonRankTermSupported r i k) (k + 1)

theorem sum_gordonRankTermSupported (r i k K : ℕ) (hi : 1 ≤ i) (hk : k ≤ K) :
    (∑ t ∈ Finset.range (K + 1), gordonRankTermSupported r i k t) =
      gordonCoefficient (r + 2) i k := by
  rw [gordonCoefficient_eq_sum_supported r i k hi]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro t ht htk
  have htk' : k < t := by simpa using htk
  have hm : ¬ (r + 1) * t ≤ k := by nlinarith
  simp [gordonRankTermSupported, hm]

@[simp] theorem gordonRankCorrection_zero (r i k : ℕ) :
    gordonRankCorrection r i k 0 = 0 := by simp [gordonRankCorrection]

@[simp] theorem gordonRankCorrection_end (r i k : ℕ) :
    gordonRankCorrection r i k (k + 1) = 0 := by
  have hm : ¬ (r + 1) * (k + 1) ≤ k := by nlinarith
  simp [gordonRankCorrection, hm]

/-- Finite telescoping establishes each interior positive-charge recurrence
from the recurrences of the preceding rank. -/
theorem gordonCoefficient_interior_of_lower (r i k : ℕ) (hi : 2 ≤ i) (hiN : i ≤ r + 1)
    (hrec : ∀ j q, 2 ≤ j → j ≤ r + 1 →
      gordonCoefficient (r + 1) j q - gordonCoefficient (r + 1) (j - 1) q =
        if j - 1 ≤ q then (MvPowerSeries.X 1 : ChargeSeries) ^ (q - (j - 1)) *
          gordonCoefficient (r + 1) (r + 1 - j + 1) (q - (j - 1)) else 0) :
    gordonCoefficient (r + 2) i (k + (i - 1)) -
      gordonCoefficient (r + 2) (i - 1) (k + (i - 1)) =
      (MvPowerSeries.X 1 : ChargeSeries) ^ k * gordonCoefficient (r + 2) (r + 3 - i) k := by
  classical
  rw [gordonCoefficient_eq_sum_supported r i _ (by omega),
    gordonCoefficient_eq_sum_supported r (i - 1) _ (by omega), ← Finset.sum_sub_distrib]
  calc
    _ = ∑ t ∈ Finset.range (k + (i - 1) + 1),
        ((MvPowerSeries.X 1 : ChargeSeries) ^ k * gordonRankTermSupported r (r + 3 - i) k t +
          (gordonRankCorrection r i (k + (i - 1)) t -
            gordonRankCorrection r i (k + (i - 1)) (t + 1))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [gordonRankTerm_telescoping r i k t hi hiN hrec]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub',
        gordonRankCorrection_zero, gordonRankCorrection_end, sub_self, add_zero,
        sum_gordonRankTermSupported r (r + 3 - i) k (k + (i - 1)) (by omega) (by omega)]

/-- The Gordon recurrence for the existing explicit multisum at every index
2≤i≤N. The first endpoint is `gordonCoefficient_first`. -/
theorem gordonCoefficient_recurrence (N i k : ℕ) (hi : 2 ≤ i) (hiN : i ≤ N) :
    gordonCoefficient N i k - gordonCoefficient N (i - 1) k =
      if i - 1 ≤ k then (MvPowerSeries.X 1 : ChargeSeries) ^ (k - (i - 1)) *
        gordonCoefficient N (N - i + 1) (k - (i - 1)) else 0 := by
  induction N generalizing i k with
  | zero => omega
  | succ N ih =>
    cases N with
    | zero => omega
    | succ r =>
      by_cases hk : i - 1 ≤ k
      · rw [if_pos hk]
        obtain ⟨q, rfl⟩ : ∃ q, k = q + (i - 1) :=
          ⟨k - (i - 1), (Nat.sub_add_cancel hk).symm⟩
        rw [Nat.add_sub_cancel_right]
        by_cases hitop : i = r + 2
        · subst i
          simpa using gordonCoefficient_top_recurrence r q
        · have hi' : i ≤ r + 1 := by omega
          have he := gordonCoefficient_interior_of_lower r i q hi hi'
            (fun j q hj hjN => ih j q hj hjN)
          simpa [show r + 2 - i + 1 = r + 3 - i by omega] using he
      · rw [if_neg hk]
        apply sub_eq_zero.mpr
        have he := gordonCoefficient_eq_previous_of_lt (r + 2) (i - 1) k
          (by omega) (by omega) (by omega)
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ i)] using he

/-- The Gordon family with the recurrence boundary value at index zero.
The explicit multisum at positive indices is unchanged. -/
def gordonFamily (N i k : ℕ) : ChargeSeries :=
  if i = 0 then 0 else gordonCoefficient N i k

@[simp] theorem gordonFamily_zero_index (N k : ℕ) : gordonFamily N 0 k = 0 := by
  simp [gordonFamily]

theorem gordonFamily_zero_charge (N i : ℕ) (hi : 1 ≤ i) : gordonFamily N i 0 = 1 := by
  simp [gordonFamily, show i ≠ 0 by omega]

/-- The coefficientwise Gordon recurrence including index one and the empty
branch at small charge, proved for the explicit multisum. -/
theorem gordonFamily_recurrence (N i k : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    gordonFamily N i k - gordonFamily N (i - 1) k =
      if i - 1 ≤ k then (MvPowerSeries.X 1 : ChargeSeries) ^ (k - (i - 1)) *
        gordonFamily N (N - i + 1) (k - (i - 1)) else 0 := by
  by_cases hi1 : i = 1
  · subst i
    have hN : N ≠ 0 := by omega
    simpa [gordonFamily, Nat.sub_add_cancel hiN, hN] using gordonCoefficient_first N k
  · have hi2 : 2 ≤ i := by omega
    simpa [gordonFamily, show i ≠ 0 by omega, show i - 1 ≠ 0 by omega,
      show N - i + 1 ≠ 0 by omega] using gordonCoefficient_recurrence N i k hi2 hiN

/-- Combining the complete exponent before taking a natural-number power
avoids any inverse of the formal variable in the alternating Gordon formula. -/
theorem gordon_exponent_nonnegative (N i j : ℕ) (hi : i ≤ N) :
    (i - 1) * j ≤ quadraticExponent N j := by
  by_cases hj : j = 0
  · subst j; simp [quadraticExponent]
  have hj2 : j ≤ j ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_left (2 * N + 1) hj2
  have hi' : i - 1 ≤ N := by omega
  have hn := Nat.mul_le_mul_right j hi'
  have he : 2 * ((i - 1) * j) + j ≤ (2 * N + 1) * j ^ 2 := by nlinarith
  unfold quadraticExponent
  omega

/-- Coefficientwise uniqueness for the Gordon recurrence. The same-charge
term at index one is resolved by cancelling `1 - v^k` in positive charge. -/
theorem gordon_recurrence_unique {S : Type*} [CommRing S] [IsDomain S]
    (v : S) (hv : ∀ k : ℕ, 0 < k → v ^ k ≠ 1) (N : ℕ) (hN : 0 < N)
    (F G : ℕ → ℕ → S)
    (hF0 : ∀ k, F 0 k = 0) (hG0 : ∀ k, G 0 k = 0)
    (hinit : ∀ i, 1 ≤ i → i ≤ N → F i 0 = G i 0)
    (hF : ∀ i k, 1 ≤ i → i ≤ N → F i k - F (i - 1) k =
      if i - 1 ≤ k then v ^ (k - (i - 1)) * F (N - i + 1) (k - (i - 1)) else 0)
    (hG : ∀ i k, 1 ≤ i → i ≤ N → G i k - G (i - 1) k =
      if i - 1 ≤ k then v ^ (k - (i - 1)) * G (N - i + 1) (k - (i - 1)) else 0) :
    ∀ k i, 1 ≤ i → i ≤ N → F i k = G i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst k; exact hinit
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hdiff (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
        F i k - G i k = F 1 k - G 1 k := by
      induction i with
      | zero => omega
      | succ i hprev =>
        by_cases hi0 : i = 0
        · subst i; rfl
        have hi1 : 1 ≤ i := by omega
        have hf := hF (i + 1) k (by omega) hiN
        have hg := hG (i + 1) k (by omega) hiN
        have hp := hprev hi1 (by omega)
        simp only [Nat.add_sub_cancel] at hf hg
        have hr : F (i + 1) k - F i k = G (i + 1) k - G i k := by
          rw [hf, hg]
          split_ifs with hle
          · rw [ih (k - i) (by omega) (N - (i + 1) + 1) (by omega) (by omega)]
          · rfl
        calc
          F (i + 1) k - G (i + 1) k = F i k - G i k := by
            linear_combination hr
          _ = _ := hp
    have hf := hF 1 k (by omega) hN
    have hg := hG 1 k (by omega) hN
    simp only [Nat.sub_self, zero_le, ↓reduceIte, Nat.sub_zero,
      Nat.sub_add_cancel hN, hF0, hG0, sub_zero] at hf hg
    have he : (1 - v ^ k) * (F 1 k - G 1 k) = 0 := by
      have hd := hdiff N hN (le_refl _)
      calc
        _ = (F 1 k - G 1 k) - v ^ k * (F N k - G N k) := by rw [hd]; ring
        _ = 0 := by rw [hf, hg]; ring
    have hz : F 1 k - G 1 k = 0 :=
      (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr (Ne.symm (hv k hkpos)))
    intro i hi hiN
    exact sub_eq_zero.mp ((hdiff i hi hiN).trans hz)

end TorusLinkHomology.HilbertSeries
