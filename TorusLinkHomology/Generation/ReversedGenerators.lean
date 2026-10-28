import TorusLinkHomology.Generation.Reversal
import TorusLinkHomology.Generation.AuxiliaryStatement
import TorusLinkHomology.MuCycles

/-!
# The reversed mu generators and the finite tail family

The tail recurrence gives a triangular change of generators with invertible
integer diagonal. This module connects auxiliary generation with the literal
cycle-generation statement of the original complex.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.Reversal

open CoefficientComplex (chi tail invNat)

theorem reversal_offset_add (N n : ℕ) (hN : 0 < N) :
    (N - 1) * n + n = N * n := by
  have hnN : n ≤ N * n := by simpa using Nat.mul_le_mul_right n hN
  rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel hnN]

private theorem mu_eq_sum (N n k : ℕ) (hk : k < n) :
    mu N n k = ∑ i : Fin n, if h : i.val ≤ k then
      (((N : R n) * (i.val : R n) - ((k - i.val : ℕ) : R n)) * u n i) •
        xi n ⟨k - i.val, by omega⟩ else 0 := by
  classical
  unfold mu
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val ≤ k
  · rw [dif_pos hi]
    rw [Finset.sum_eq_single (⟨k - i.val, by omega⟩ : Fin n)]
    · simp only [show i.val + (k - i.val) = k by omega, ↓reduceIte]
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      apply Fin.ext
      change j.val = k - i.val
      omega
    · simp
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    exact if_neg (by omega)

/-- The coefficients in the extended-tail recursion. -/
def tailCoefficient (N n j : ℕ) (i : Fin n) : R n :=
  ((((N + 1 : ℕ) : R n) * ((i.val + 1 : ℕ) : R n) - (j : R n)) *
    CoefficientComplex.e n i)

/-- The initial-generator part of the recurrence, with the sign of the
reversed mu cycle. -/
def nu (N n ell j : ℕ) : A n :=
  -(∑ i : Fin n, tailCoefficient N n j i • chi n ell (j - (i.val + 1)))

/-- Coefficient reversal sends each named mu to its specified initial-tail
combination, with the integer signs retained. -/
theorem reverseChains_mu (N n k : ℕ) (hN : 0 < N) (hk : k < n) :
    reverseChains n (mu N n k) = nu N n ((N - 1) * n) ((N + 1) * n - k) := by
  classical
  have hoff := reversal_offset_add N n hN
  have htop : (N + 1) * n = N * n + n := by rw [Nat.add_mul, one_mul]
  rw [mu_eq_sum N n k hk, map_sum, nu, ← Finset.sum_neg_distrib]
  apply Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin n))
  intro i
  change reverseChains n (if h : i.val ≤ k then _ else _) =
    -(tailCoefficient N n ((N + 1) * n - k) i.rev •
      chi n ((N - 1) * n) ((N + 1) * n - k - (i.rev.val + 1)))
  have hir : i.rev.val + 1 = n - i.val := by simp only [Fin.val_rev]; omega
  by_cases hi : i.val ≤ k
  · rw [dif_pos hi, reverseChains_smul, reverseChains_xi]
    have hb : (N - 1) * n < (N + 1) * n - k - (i.rev.val + 1) ∧
        (N + 1) * n - k - (i.rev.val + 1) ≤ (N - 1) * n + n := by
      have := i.isLt
      omega
    rw [chi, dif_pos hb]
    have hind :
        (⟨k - i.val, by omega⟩ : Fin n).rev =
          ⟨(N + 1) * n - k - (i.rev.val + 1) - (N - 1) * n - 1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    rw [hind, ← neg_smul]
    congr 1
    simp only [map_mul, map_sub, map_natCast, reverseCoefficients_u, tailCoefficient]
    rw [Nat.cast_sub (by omega : k ≤ (N + 1) * n), Nat.cast_mul,
      hir, Nat.cast_sub (Nat.le_of_lt i.isLt), Nat.cast_sub hi]
    push_cast
    ring
  · rw [dif_neg hi, map_zero]
    have hb : ¬((N - 1) * n < (N + 1) * n - k - (i.rev.val + 1) ∧
        (N + 1) * n - k - (i.rev.val + 1) ≤ (N - 1) * n + n) := by
      have := i.isLt
      omega
    rw [chi, dif_neg hb, smul_zero, neg_zero]

/-- The tail recursion solved using the reversed generator and strictly
earlier tails. Its diagonal coefficient is the invertible integer `j`. -/
theorem tail_eq_nu_add_earlier (N n j : ℕ) (hN : 0 < N) (hj : N * n < j) :
    tail N n ((N - 1) * n) j = invNat n j •
      (-nu N n ((N - 1) * n) j + ∑ i : Fin n,
        if N * n < j - (i.val + 1) then
          tailCoefficient N n j i • tail N n ((N - 1) * n) (j - (i.val + 1))
        else 0) := by
  classical
  have hoff := reversal_offset_add N n hN
  rw [CoefficientComplex.tail_eq_of_gt _ _ _ _ (by omega)]
  congr 1
  change (∑ i : Fin n, tailCoefficient N n j i •
    tail N n ((N - 1) * n) (j - (i.val + 1))) = _
  rw [nu, neg_neg, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : N * n < j - (i.val + 1)
  · rw [if_pos hi, chi, dif_neg (by omega), smul_zero, zero_add]
  · rw [if_neg hi, add_zero, CoefficientComplex.tail_eq_chi _ _ _ _ (by omega)]

/-- Preimage of a coefficient subalgebra under semilinear reversal. -/
def reverseSubalgebra {n : ℕ} (S : Subalgebra (R n) (A n)) :
    Subalgebra (R n) (A n) where
  toSubsemiring := S.toSubsemiring.comap (reverseChains n)
  algebraMap_mem' r := by
    change reverseChains n (algebraMap (R n) (A n) r) ∈ S
    rw [reverseChains_algebraMap]
    exact S.algebraMap_mem _

@[simp] theorem mem_reverseSubalgebra {n : ℕ} (S : Subalgebra (R n) (A n)) (x : A n) :
    x ∈ reverseSubalgebra S ↔ reverseChains n x ∈ S := Iff.rfl

theorem nu_mem_reversed_muSubalgebra (N n j : ℕ) (hN : 0 < N)
    (hj : N * n < j) (hj' : j < (N + 1) * n) :
    nu N n ((N - 1) * n) j ∈ reverseSubalgebra (muSubalgebra N n) := by
  have htop : (N + 1) * n = N * n + n := by rw [Nat.add_mul, one_mul]
  let k := (N + 1) * n - j
  have hk : k < n := by dsimp [k]; omega
  have hk0 : 1 ≤ k := by dsimp [k]; omega
  have hkj : (N + 1) * n - k = j := by dsimp [k]; omega
  have hmu := reverseChains_mu N n k hN hk
  rw [hkj] at hmu
  change reverseChains n (nu N n ((N - 1) * n) j) ∈ muSubalgebra N n
  rw [← hmu, reverseChains_involutive]
  exact Algebra.subset_adjoin ⟨k, hk0, hk, rfl⟩

/-- Triangular induction: each tail in the finite list is generated by the
reversed mu elements over the coefficient ring. -/
theorem finite_tail_mem_reversed_muSubalgebra (N n j : ℕ) (hN : 0 < N)
    (hj : N * n < j) (hj' : j < (N + 1) * n) :
    tail N n ((N - 1) * n) j ∈ reverseSubalgebra (muSubalgebra N n) := by
  classical
  induction j using Nat.strong_induction_on with
  | h j ih =>
    rw [tail_eq_nu_add_earlier N n j hN hj]
    apply Subalgebra.smul_mem
    apply Subalgebra.add_mem
    · exact Subalgebra.neg_mem _ (nu_mem_reversed_muSubalgebra N n j hN hj hj')
    · apply Subalgebra.sum_mem
      intro i _
      split_ifs with hi
      · apply Subalgebra.smul_mem
        exact ih _ (by omega) hi (by omega)
      · exact Subalgebra.zero_mem _

/-- Every designated auxiliary tail reverses into the original mu algebra. -/
theorem tailSubalgebra_le_reversed_muSubalgebra (N n : ℕ) (hN : 0 < N) (hn : 0 < n) :
    CoefficientComplex.tailSubalgebra N n ((N - 1) * n) ≤
      reverseSubalgebra (muSubalgebra N n) := by
  have hoff := reversal_offset_add N n hN
  rw [CoefficientComplex.tailSubalgebra_eq_adjoin_finite _ _ _ (by omega)]
  apply Algebra.adjoin_le
  rintro _ ⟨j, hj, hj', rfl⟩
  exact finite_tail_mem_reversed_muSubalgebra N n j hN hj hj'

/-- Auxiliary tail generation at the reversal offset implies the exact
original cycle-generation statement, without assuming either public theorem. -/
theorem cycleGeneration_of_tailGeneration (N n : ℕ) (hN : 0 < N) (hn : 0 < n)
    (hgen : CoefficientComplex.TailGeneration N n ((N - 1) * n)) :
    (∀ k : ℕ, 1 ≤ k → k < n → d N n (mu N n k) = 0) ∧
    (∀ a : A n, d N n a = 0 →
      ∃ p : A n, p ∈ muSubalgebra N n ∧ ∃ b : A n, a = p + d N n b) := by
  refine ⟨fun k _ hk => mu_is_cycle N n k hk, ?_⟩
  intro x hx
  have hx' : CoefficientComplex.d N n ((N - 1) * n) (reverseChains n x) = 0 := by
    rw [reverseChains_d N n hN, hx, map_zero]
  obtain ⟨p, hp, b, hxb⟩ := hgen _ hx'
  refine ⟨reverseChains n p, tailSubalgebra_le_reversed_muSubalgebra N n hN hn hp,
    reverseChains n b, ?_⟩
  have hb : reverseChains n (CoefficientComplex.d N n ((N - 1) * n) b) =
      d N n (reverseChains n b) := by
    have h := congrArg (reverseChains n) (reverseChains_d N n hN (reverseChains n b))
    simpa only [reverseChains_involutive] using h
  have h := congrArg (reverseChains n) hxb
  simpa only [reverseChains_involutive, map_add, hb] using h

end TorusLinkHomology.Reversal
