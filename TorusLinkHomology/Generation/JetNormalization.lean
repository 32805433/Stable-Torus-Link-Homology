import TorusLinkHomology.MuCycles

/-!
# Factorial normalization of the differentiated universal cycle

UEI-012/013: write `Uᵢ = i! uᵢ` and `Yᵢ = i! ξᵢ`. The formal `k`th
derivative of `B = U₀Y₁ - N U₁Y₀` is represented by its finite binomial
Leibniz formula. When `k + 1 < n`, every jet that occurs lies in the given
finite algebra. No derivation of the truncated algebra is defined.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.UniversalJets

/-- The ordinary even jet in divided coordinates. -/
def evenJet (n : ℕ) (i : Fin n) : R n := (i.val.factorial : R n) * u n i

/-- The ordinary odd jet in divided coordinates. -/
def oddJet (n : ℕ) (i : Fin n) : A n := (i.val.factorial : R n) • xi n i

/-- Contribution of `Dᵏ(U₀Y₁)` to `UₐY_b`; at `b=0` this term is absent. -/
def rightLeibnizCoefficient (k a b : ℕ) : ℕ :=
  if b = 0 then 0 else k.choose a

/-- Contribution of `Dᵏ(U₁Y₀)` to `UₐY_b`; at `a=0` this term is absent. -/
def leftLeibnizCoefficient (k a _b : ℕ) : ℕ :=
  if a = 0 then 0 else k.choose (a - 1)

/-- The signed binomial coefficient of `UₐY_b` in the Leibniz formula. -/
def bDerivativeCoefficient (N k a b : ℕ) : ℤ :=
  (rightLeibnizCoefficient k a b : ℤ) -
    (N : ℤ) * (leftLeibnizCoefficient k a b : ℤ)

/-- The finite explicit expression for `Dᵏ(U₀Y₁ - N U₁Y₀)`.
Both binomial endpoint conventions are explicit. It is the full formal jet
derivative whenever `k + 1 < n`; outside that range it retains only available
jet pairs, and is not asserted to be an iterate of a truncated derivation. -/
def bDerivative (N n k : ℕ) : A n :=
  ∑ a : Fin n, ∑ b : Fin n,
    if a.val + b.val = k + 1 then
      ((bDerivativeCoefficient N k a.val b.val : R n) * evenJet n a) • oddJet n b
    else 0

theorem rightLeibnizCoefficient_factorial (k a b : ℕ) (hab : a + b = k + 1) :
    rightLeibnizCoefficient k a b * a.factorial * b.factorial = k.factorial * b := by
  rcases b with _ | b
  · simp [rightLeibnizCoefficient]
  · have hk : k = a + b := by omega
    subst k
    have h := Nat.choose_mul_factorial_mul_factorial (n := a + b) (k := a) (by omega)
    rw [Nat.add_sub_cancel_left] at h
    simp only [rightLeibnizCoefficient, Nat.succ_ne_zero, ↓reduceIte, Nat.factorial_succ]
    calc
      (a + b).choose a * a.factorial * ((b + 1) * b.factorial) =
          ((a + b).choose a * a.factorial * b.factorial) * (b + 1) := by ring
      _ = (a + b).factorial * (b + 1) := by rw [h]

theorem leftLeibnizCoefficient_factorial (k a b : ℕ) (hab : a + b = k + 1) :
    leftLeibnizCoefficient k a b * a.factorial * b.factorial = k.factorial * a := by
  rcases a with _ | a
  · simp [leftLeibnizCoefficient]
  · have hk : k = a + b := by omega
    subst k
    have h := Nat.choose_mul_factorial_mul_factorial (n := a + b) (k := a) (by omega)
    rw [Nat.add_sub_cancel_left] at h
    simp only [leftLeibnizCoefficient, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      Nat.factorial_succ]
    calc
      (a + b).choose a * ((a + 1) * a.factorial) * b.factorial =
          ((a + b).choose a * a.factorial * b.factorial) * (a + 1) := by ring
      _ = (a + b).factorial * (a + 1) := by rw [h]

/-- UEI-013's coefficient identity, with both boundary cases included and
subtraction performed in the coefficient ring. -/
theorem bDerivativeCoefficient_factorial {S : Type*} [CommRing S]
    (N k a b : ℕ) (hab : a + b = k + 1) :
    (bDerivativeCoefficient N k a b : S) * (a.factorial : S) * (b.factorial : S) =
      -(k.factorial : S) * ((N : S) * (a : S) - (b : S)) := by
  have hr : (rightLeibnizCoefficient k a b : S) * (a.factorial : S) * (b.factorial : S) =
      (k.factorial : S) * (b : S) := by
    simpa only [Nat.cast_mul] using congrArg (fun z : ℕ => (z : S))
      (rightLeibnizCoefficient_factorial k a b hab)
  have hl : (leftLeibnizCoefficient k a b : S) * (a.factorial : S) * (b.factorial : S) =
      (k.factorial : S) * (a : S) := by
    simpa only [Nat.cast_mul] using congrArg (fun z : ℕ => (z : S))
      (leftLeibnizCoefficient_factorial k a b hab)
  simp only [bDerivativeCoefficient, Int.cast_sub, Int.cast_natCast, Int.cast_mul]
  calc
    _ = ((rightLeibnizCoefficient k a b : S) * a.factorial * b.factorial) -
        N * ((leftLeibnizCoefficient k a b : S) * a.factorial * b.factorial) := by ring
    _ = _ := by rw [hr, hl]; ring

/-- UEI-013: the differentiated ordinary-jet cycle is the named cycle times
the negative factorial. The finite formula makes this identity valid even
for the truncation outside the range used for universal jets. -/
theorem bDerivative_eq_smul_mu (N n k : ℕ) :
    bDerivative N n k = -(k.factorial : R n) • mu N n (k + 1) := by
  unfold bDerivative mu
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a.val + b.val = k + 1
  · simp only [if_pos hab, evenJet, oddJet, smul_smul]
    congr 1
    calc
      _ = ((bDerivativeCoefficient N k a.val b.val : R n) *
          a.val.factorial * b.val.factorial) * u n a := by ring
      _ = _ := by rw [bDerivativeCoefficient_factorial N k a.val b.val hab]; ring
  · simp [hab]

/-- The indexing form used in the universal one-cycle basis. -/
theorem bDerivative_pred_eq_smul_mu (N n j : ℕ) (hj : 1 ≤ j) :
    bDerivative N n (j - 1) = -((j - 1).factorial : R n) • mu N n j := by
  simpa only [Nat.sub_add_cancel hj] using bDerivative_eq_smul_mu N n (j - 1)

/-- The inverse normalization uses only a nonzero rational factorial. -/
theorem mu_eq_invFactorial_smul_bDerivative (N n k : ℕ) :
    mu N n (k + 1) =
      algebraMap ℚ (R n) (-((k.factorial : ℚ)⁻¹)) • bDerivative N n k := by
  rw [bDerivative_eq_smul_mu, smul_smul]
  have hfac : (k.factorial : R n) = algebraMap ℚ (R n) (k.factorial : ℚ) := by simp
  have hnonzero : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [hfac, map_neg, neg_mul_neg, ← map_mul, inv_mul_cancel₀ hnonzero, map_one, one_smul]

/-- UEI-013 product normalization, with the product order retained. -/
theorem bDerivative_orderedProduct_eq (N n : ℕ) (indices : List ℕ) :
    (indices.map (bDerivative N n)).prod =
      (indices.map (fun k => -(k.factorial : R n))).prod •
        (indices.map (fun k => mu N n (k + 1))).prod := by
  induction indices with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.prod_cons, bDerivative_eq_smul_mu, ih]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/-- The same ordered-product formula with the sign separated from the
positive factorial factors, as in UEI-013. -/
theorem bDerivative_orderedProduct_eq_signed (N n : ℕ) (indices : List ℕ) :
    (indices.map (bDerivative N n)).prod =
      ((-1 : R n) ^ indices.length * (indices.map (fun k => (k.factorial : R n))).prod) •
        (indices.map (fun k => mu N n (k + 1))).prod := by
  rw [bDerivative_orderedProduct_eq]
  congr 1
  induction indices with
  | nil => simp
  | cons k ks ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, ih]
    ring

/-- At derivative order zero the explicit Leibniz expression is exactly
the defining universal one-cycle `B`. -/
theorem bDerivative_zero (N n : ℕ) :
    bDerivative N (n + 2) 0 =
      evenJet (n + 2) 0 • oddJet (n + 2) 1 -
        ((N : R (n + 2)) * evenJet (n + 2) 1) • oddJet (n + 2) 0 := by
  have h (x y : ℕ) : x + (1 + (1 + (y + 2))) ≠ 1 := by omega
  simp [bDerivative_eq_smul_mu, mu, evenJet, oddJet, Fin.sum_univ_succ,
    Nat.add_assoc, h, sub_eq_add_neg]

/-- Every differentiated jet expression in the valid finite range is closed. -/
theorem bDerivative_is_cycle (N n k : ℕ) (hk : k + 1 < n) :
    d N n (bDerivative N n k) = 0 := by
  rw [bDerivative_eq_smul_mu, map_smul, mu_is_cycle N n (k + 1) hk, smul_zero]

end TorusLinkHomology.UniversalJets
