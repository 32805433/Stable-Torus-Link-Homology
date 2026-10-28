import TorusLinkHomology.Generation.CoefficientSeries

/-! # The ordinary Euler-jet Leibniz formula

The upper exponents add under multiplication, and the coefficient algebra
need not be commutative.
-/

noncomputable section

namespace TorusLinkHomology.CoefficientSeries

open scoped BigOperators

variable {A : Type*} [Ring A]

theorem iterate_shiftedEuler_mul (b c : ℤ) (k : ℕ) (f g : PowerSeries A) :
    (shiftedEuler (b + c))^[k] (f * g) =
      ∑ ij ∈ Finset.antidiagonal k, k.choose ij.1 •
        ((shiftedEuler b)^[ij.1] f * (shiftedEuler c)^[ij.2] g) := by
  ext t : 1
  simp only [coeff_iterate_shiftedEuler, map_sum, map_zsmul, PowerSeries.coeff_mul,
    coeff_iterate_shiftedEuler, Finset.smul_sum, ← natCast_zsmul,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [← Finset.sum_smul]
  congr 1
  have hab' := Finset.mem_antidiagonal.mp hab
  have hsplit : b + c - (t : ℤ) = (b - (ab.1 : ℤ)) + (c - (ab.2 : ℤ)) := by omega
  rw [hsplit]
  simpa only [nsmul_eq_mul, mul_comm] using
    (Commute.all (b - (ab.1 : ℤ)) (c - (ab.2 : ℤ))).add_pow' k

end TorusLinkHomology.CoefficientSeries

namespace TorusLinkHomology.UniversalJets

open scoped BigOperators

variable {M : Type*} [AddCommMonoid M]

/-- Reindex the positive second-jet endpoint of the finite Leibniz sum. -/
theorem sum_fin_right_jet_shift (n k : ℕ) (hk : k + 1 < n) (F : ℕ → ℕ → M) :
    (∑ a : Fin n, ∑ b : Fin n,
      if a.val + b.val = k + 1 then
        (if b.val = 0 then 0 else k.choose a.val) • F a.val b.val else 0) =
      ∑ ij ∈ Finset.antidiagonal k, k.choose ij.1 • F ij.1 (ij.2 + 1) := by
  let f : ℕ → ℕ → M := fun a b =>
    if a + b = k + 1 then (if b = 0 then 0 else k.choose a) • F a b else 0
  change (∑ a : Fin n, ∑ b : Fin n, f a.val b.val) = _
  simp_rw [Fin.sum_univ_eq_sum_range (f _) n]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.range n, f a b) n]
  dsimp only [f]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => k.choose i • F i (j + 1)) k]
  have inner (a : ℕ) :
      (∑ b ∈ Finset.range n,
        if a + b = k + 1 then (if b = 0 then 0 else k.choose a) • F a b else 0) =
        if a < k + 1 then k.choose a • F a (k - a + 1) else 0 := by
    by_cases ha : a < k + 1
    · rw [if_pos ha, Finset.sum_eq_single (k - a + 1)]
      · simp [show a + (k - a + 1) = k + 1 by omega]
      · intro b _ hne
        exact if_neg (by omega)
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
    · rw [if_neg ha]
      apply Finset.sum_eq_zero
      intro b _
      by_cases hab : a + b = k + 1
      · have hb : b = 0 := by omega
        simp [hb]
      · exact if_neg hab
  simp_rw [inner]
  rw [← Finset.sum_subset (Finset.range_mono (by omega : k + 1 ≤ n))]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [if_pos (Finset.mem_range.mp ha)]
  · intro a _ ha
    exact if_neg (fun h => ha (Finset.mem_range.mpr h))

/-- Reindex the positive first-jet endpoint, preserving the factor order. -/
theorem sum_fin_left_jet_shift (n k : ℕ) (hk : k + 1 < n) (F : ℕ → ℕ → M) :
    (∑ a : Fin n, ∑ b : Fin n,
      if a.val + b.val = k + 1 then
        (if a.val = 0 then 0 else k.choose (a.val - 1)) • F a.val b.val else 0) =
      ∑ ij ∈ Finset.antidiagonal k, k.choose ij.1 • F (ij.1 + 1) ij.2 := by
  have h := sum_fin_right_jet_shift n k hk (fun a b => F b a)
  rw [Finset.sum_comm] at h
  conv_rhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  trans (∑ ij ∈ Finset.antidiagonal k, k.choose ij.1 • F (ij.2 + 1) ij.1)
  · rw [← h]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : a.val + b.val = k + 1
    · have hab' : b.val + a.val = k + 1 := by omega
      rw [if_pos hab, if_pos hab']
      by_cases ha : a.val = 0
      · simp [ha]
      · rw [if_neg ha, if_neg ha]
        have hbk : b.val ≤ k := by omega
        have ha' : a.val - 1 = k - b.val := by omega
        rw [ha', Nat.choose_symm hbk]
    · rw [if_neg hab, if_neg (by omega : ¬b.val + a.val = k + 1)]
  · apply Finset.sum_congr rfl
    intro ij hij
    have hij' := Finset.mem_antidiagonal.mp hij
    dsimp only [Prod.swap]
    congr 1
    have hj : ij.2 = k - ij.1 := by omega
    rw [hj, Nat.choose_symm (by omega : ij.1 ≤ k)]

end TorusLinkHomology.UniversalJets
