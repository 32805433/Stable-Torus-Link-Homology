import TorusLinkHomology.HilbertSeries.ShortRange
import TorusLinkHomology.HilbertSeries.FiniteNumerator
import Mathlib.Algebra.Ring.GeomSum

/-! Series identities from graded rank–nullity and short-range cycle coordinates. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- The trigraded series of the actual chain spaces. -/
def chainHilbertSeries (N n : ℕ) : Series :=
  fun e => (Module.finrank ℚ (chainPiece N n (e 0) (e 1) (e 2)) : ℚ)

/-- The trigraded series of the actual cycle spaces. -/
def cycleHilbertSeries (N n : ℕ) : Series :=
  fun e => (Module.finrank ℚ (cyclePiece N n (e 0) (e 1) (e 2)) : ℚ)

/-- The trigraded series of homogeneous boundaries. -/
def boundaryHilbertSeries (N n : ℕ) : Series :=
  fun e => (Module.finrank ℚ (boundaryPiece N n (e 0) (e 1) (e 2)) : ℚ)

/-- Rank–nullity on homogeneous cycles, as a formal series identity. -/
theorem cycleHilbertSeries_eq (N n : ℕ) :
    cycleHilbertSeries N n = hilbertSeries N n + boundaryHilbertSeries N n := by
  ext e
  simpa only [map_add, MvPowerSeries.coeff_apply,
    cycleHilbertSeries, hilbertSeries, boundaryHilbertSeries, Nat.cast_add] using
    congrArg (fun k : ℕ => (k : ℚ))
      (finrank_cyclePiece_eq_homology_add_boundary N n (e 0) (e 1) (e 2))

set_option maxHeartbeats 800000 in
/-- Multiplication by the exterior-degree variable implements the boundary shift. -/
theorem chainHilbertSeries_eq (N n : ℕ) :
    chainHilbertSeries N n = cycleHilbertSeries N n +
      (MvPowerSeries.X 2 : Series) * boundaryHilbertSeries N n := by
  classical
  ext e
  rw [map_add, MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
  by_cases he : e 2 = 0
  · have hn : ¬ Finsupp.single (2 : Fin 3) 1 ≤ e := by
      intro h
      have h' := h 2
      simp [he] at h'
    rw [if_neg hn, add_zero]
    simp only [MvPowerSeries.coeff_apply, chainHilbertSeries, cycleHilbertSeries]
    rw [he, finrank_chainPiece_zero]
  · have hy : Finsupp.single (2 : Fin 3) 1 ≤ e := by
      intro i
      fin_cases i <;> simp
      omega
    rw [if_pos hy, one_mul]
    have h0 : ((e - Finsupp.single (2 : Fin 3) 1) : Fin 3 →₀ ℕ) 0 = e 0 := by simp
    have h1 : ((e - Finsupp.single (2 : Fin 3) 1) : Fin 3 →₀ ℕ) 1 = e 1 := by simp
    have h2 : ((e - Finsupp.single (2 : Fin 3) 1) : Fin 3 →₀ ℕ) 2 = e 2 - 1 := by simp
    simp only [MvPowerSeries.coeff_apply, chainHilbertSeries, cycleHilbertSeries,
      boundaryHilbertSeries]
    rw [h0, h1, h2]
    obtain ⟨h, hh⟩ := Nat.exists_eq_succ_of_ne_zero he
    rw [hh, Nat.succ_eq_add_one, Nat.add_sub_cancel]
    simpa only [Nat.cast_add] using
      congrArg (fun k : ℕ => (k : ℚ)) (finrank_chainPiece_succ N n (e 0) (e 1) h)

/-- The Hilbert series of homology follows from chains and cycles without
inverting the exterior-degree variable. -/
theorem hilbertSeries_from_chains_and_cycles (N n : ℕ) :
    (MvPowerSeries.X 2 : Series) * hilbertSeries N n =
      (1 + MvPowerSeries.X 2) * cycleHilbertSeries N n - chainHilbertSeries N n := by
  rw [chainHilbertSeries_eq, cycleHilbertSeries_eq]
  ring


/-- Encode the three monomial degrees as a power-series exponent. -/
def boundedDegree (N n A : ℕ) (m : BoundedMonomial n A) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 ((∑ i, (m.1 i).val) + N * m.2.card) +
    Finsupp.single 1 ((∑ i, i.val * (m.1 i).val) + ∑ i ∈ m.2, i.val) +
      Finsupp.single 2 m.2.card

theorem boundedDegree_eq_iff (N n : ℕ) (e : Fin 3 →₀ ℕ) (m : BoundedMonomial n (e 0)) :
    boundedDegree N n (e 0) m = e ↔ HasDegree N n (e 0) (e 1) (e 2) m := by
  constructor
  · intro he
    constructor
    · simpa [boundedDegree] using congrArg (fun e => e 0) he
    constructor
    · simpa [boundedDegree] using congrArg (fun e => e 1) he
    · simpa [boundedDegree] using congrArg (fun e => e 2) he
  · rintro ⟨ha, hb, hh⟩
    ext i
    fin_cases i
    · simpa [boundedDegree] using ha
    · simpa [boundedDegree] using hb
    · simpa [boundedDegree] using hh

/-- Finite polynomial truncation of chains whose exterior indices lie in S. -/
def truncatedChainSeries (N n A : ℕ) (S : Finset (Fin n)) : Series :=
  ∑ m : BoundedMonomial n A,
    if m.2 ⊆ S then MvPowerSeries.monomial (boundedDegree N n A m) 1 else 0

theorem coeff_truncatedChainSeries (N n A : ℕ) (S : Finset (Fin n))
    (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (truncatedChainSeries N n A S) =
      (Nat.card {m : BoundedMonomial n A //
        boundedDegree N n A m = e ∧ m.2 ⊆ S} : ℚ) := by
  classical
  simp only [truncatedChainSeries, map_sum, apply_ite, map_zero,
    MvPowerSeries.coeff_monomial, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hs : m.2 ⊆ S <;> by_cases hd : boundedDegree N n A m = e <;>
    simp_all only [ite_true, ite_false, and_self, and_false, and_true, eq_comm]


/-- The monomial recording the degree of u_i. -/
def evenGeneratorSeries (i : ℕ) : Series :=
  MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 i) 1

/-- The monomial recording the degree of ξ_i. -/
def oddGeneratorSeries (N i : ℕ) : Series :=
  MvPowerSeries.monomial
    (Finsupp.single 0 N + Finsupp.single 1 i + Finsupp.single 2 1) 1

theorem evenGeneratorSeries_eq (i : ℕ) :
    evenGeneratorSeries i = (MvPowerSeries.X 0 : Series) * MvPowerSeries.X 1 ^ i := by
  rw [MvPowerSeries.X_pow_eq]
  simp only [evenGeneratorSeries, MvPowerSeries.X,
    MvPowerSeries.monomial_mul_monomial, mul_one]

theorem oddGeneratorSeries_eq (N i : ℕ) :
    oddGeneratorSeries N i =
      (MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ N * MvPowerSeries.X 1 ^ i := by
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq]
  simp only [oddGeneratorSeries, MvPowerSeries.X,
    MvPowerSeries.monomial_mul_monomial, mul_one]
  apply congrArg (fun d : Fin 3 →₀ ℕ => MvPowerSeries.monomial d (1 : ℚ))
  abel

theorem boundedDegree_monomial (N n A : ℕ) (m : BoundedMonomial n A) :
    MvPowerSeries.monomial (boundedDegree N n A m) (1 : ℚ) =
      (∏ i : Fin n, evenGeneratorSeries i.val ^ (m.1 i).val) *
        ∏ i ∈ m.2, oddGeneratorSeries N i.val := by
  simp only [evenGeneratorSeries, oddGeneratorSeries, MvPowerSeries.monomial_pow,
    one_pow, MvPowerSeries.prod_monomial, Finset.prod_const_one,
    MvPowerSeries.monomial_mul_monomial, mul_one]
  apply congrArg (fun d : Fin 3 →₀ ℕ => MvPowerSeries.monomial d (1 : ℚ))
  ext j
  fin_cases j
  · simp [boundedDegree, Finset.sum_add_distrib, mul_comm]
  · simp [boundedDegree, Finset.sum_add_distrib, mul_comm]
  · simp [boundedDegree]

/-- Factor the finite monomial enumerator into polynomial and exterior factors. -/
theorem truncatedChainSeries_factor (N n A : ℕ) (S : Finset (Fin n)) :
    truncatedChainSeries N n A S =
      (∏ i : Fin n, ∑ k : Fin (A + 1), evenGeneratorSeries i.val ^ k.val) *
        ∏ i ∈ S, (1 + oddGeneratorSeries N i.val) := by
  classical
  rw [Fintype.prod_sum, Finset.prod_one_add, Finset.sum_mul]
  unfold truncatedChainSeries
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  simp only [boundedDegree_monomial]
  rw [← Finset.sum_filter]
  congr 1
  ext s
  simp


theorem exponent_le_of_boundedDegree (N n A : ℕ) (m : BoundedMonomial n A)
    (e : Fin 3 →₀ ℕ) (hm : boundedDegree N n A m = e) (i : Fin n) :
    (m.1 i).val ≤ e 0 := by
  have ha : (∑ j, (m.1 j).val) + N * m.2.card = e 0 := by
    simpa [boundedDegree] using congrArg (fun e => e 0) hm
  calc
    (m.1 i).val ≤ ∑ j, (m.1 j).val := Finset.single_le_sum (f := fun j : Fin n => (m.1 j).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ e 0 := by omega

/-- Changing a sufficiently large exponent bound does not change the fiber. -/
def boundedDegreeEquiv (N n A B : ℕ) (e : Fin 3 →₀ ℕ)
    (hA : e 0 ≤ A) (hB : e 0 ≤ B) (S : Finset (Fin n)) :
    {m : BoundedMonomial n A // boundedDegree N n A m = e ∧ m.2 ⊆ S} ≃
      {m : BoundedMonomial n B // boundedDegree N n B m = e ∧ m.2 ⊆ S} where
  toFun m := ⟨(fun i => ⟨(m.val.1 i).val, Nat.lt_succ_of_le
      ((exponent_le_of_boundedDegree N n A m.val e m.property.1 i).trans hB)⟩, m.val.2),
    m.property.1, m.property.2⟩
  invFun m := ⟨(fun i => ⟨(m.val.1 i).val, Nat.lt_succ_of_le
      ((exponent_le_of_boundedDegree N n B m.val e m.property.1 i).trans hA)⟩, m.val.2),
    m.property.1, m.property.2⟩
  left_inv m := by
    apply Subtype.ext
    apply Prod.ext
    · funext i; rfl
    · rfl
  right_inv m := by
    apply Subtype.ext
    apply Prod.ext
    · funext i; rfl
    · rfl

theorem coeff_truncatedChainSeries_stable (N n A B : ℕ) (S : Finset (Fin n))
    (e : Fin 3 →₀ ℕ) (hA : e 0 ≤ A) (hB : e 0 ≤ B) :
    MvPowerSeries.coeff e (truncatedChainSeries N n A S) =
      MvPowerSeries.coeff e (truncatedChainSeries N n B S) := by
  rw [coeff_truncatedChainSeries, coeff_truncatedChainSeries,
    Nat.card_congr (boundedDegreeEquiv N n A B e hA hB S)]

theorem coeff_chainHilbertSeries_truncated (N n A : ℕ) (e : Fin 3 →₀ ℕ)
    (he : e 0 ≤ A) :
    MvPowerSeries.coeff e (chainHilbertSeries N n) =
      MvPowerSeries.coeff e (truncatedChainSeries N n A Finset.univ) := by
  classical
  rw [← coeff_truncatedChainSeries_stable N n (e 0) A Finset.univ e le_rfl he]
  rw [coeff_truncatedChainSeries]
  simp only [MvPowerSeries.coeff_apply, chainHilbertSeries]
  rw [finrank_chainPiece]
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun m => by simp [boundedDegree_eq_iff])

theorem coeff_cycleHilbertSeries_truncated (N n A : ℕ) (hn : n ≤ N)
    (e : Fin 3 →₀ ℕ) (he : e 0 ≤ A) :
    MvPowerSeries.coeff e (cycleHilbertSeries N (n + 1)) =
      MvPowerSeries.coeff e
        (truncatedChainSeries (N + 1) (n + 1) A (Finset.univ.erase 0)) := by
  classical
  rw [← coeff_truncatedChainSeries_stable (N + 1) (n + 1) (e 0) A
    (Finset.univ.erase 0) e le_rfl he]
  rw [coeff_truncatedChainSeries]
  simp only [MvPowerSeries.coeff_apply, cycleHilbertSeries]
  rw [finrank_cyclePiece_shortRange N n (e 0) (e 1) (e 2) hn]
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun m => by simp [boundedDegree_eq_iff,
    Finset.subset_erase, Finset.subset_univ])


/-- Clearing a finite geometric sum leaves only terms beyond the truncation. -/
theorem denominator_mul_truncatedChainSeries (N n A : ℕ) (S : Finset (Fin n)) :
    (∏ i : Fin n, (1 - evenGeneratorSeries i.val)) * truncatedChainSeries N n A S =
      (∏ i : Fin n, (1 - evenGeneratorSeries i.val ^ (A + 1))) *
        ∏ i ∈ S, (1 + oddGeneratorSeries N i.val) := by
  rw [truncatedChainSeries_factor, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Fin.sum_univ_eq_sum_range]
  exact mul_neg_geom_sum _ _

theorem coeff_even_power_mul_zero (i A : ℕ) (e : Fin 3 →₀ ℕ) (f : Series)
    (he : e 0 ≤ A) :
    MvPowerSeries.coeff e (evenGeneratorSeries i ^ (A + 1) * f) = 0 := by
  classical
  rw [evenGeneratorSeries, MvPowerSeries.monomial_pow, MvPowerSeries.coeff_monomial_mul]
  have hn : ¬ (A + 1) • (Finsupp.single (0 : Fin 3) 1 + Finsupp.single 1 i) ≤ e := by
    intro h
    have h0 := h 0
    simp at h0
    omega
  rw [if_neg hn]

theorem coeff_truncation_correction (n A : ℕ) (S : Finset (Fin n))
    (e : Fin 3 →₀ ℕ) (f : Series) (he : e 0 ≤ A) :
    MvPowerSeries.coeff e ((∏ i ∈ S, (1 - evenGeneratorSeries i.val ^ (A + 1))) * f) =
      MvPowerSeries.coeff e f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, mul_assoc, sub_mul, one_mul, map_sub,
      coeff_even_power_mul_zero i.val A e _ he, sub_zero, ih]

theorem coeff_mul_congr_below (e : Fin 3 →₀ ℕ) (f g k : Series)
    (h : ∀ d ≤ e, MvPowerSeries.coeff d f = MvPowerSeries.coeff d g) :
    MvPowerSeries.coeff e (k * f) = MvPowerSeries.coeff e (k * g) := by
  classical
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have he : p.1 + p.2 = e := Finset.mem_antidiagonal.mp hp
  rw [h p.2 (by rw [← he]; exact le_add_self)]

/-- Chain monomial counting, with its polynomial denominator cleared. -/
theorem chainHilbertSeries_product (N n : ℕ) :
    (∏ i : Fin n, (1 - evenGeneratorSeries i.val)) * chainHilbertSeries N n =
      ∏ i : Fin n, (1 + oddGeneratorSeries N i.val) := by
  ext e
  rw [coeff_mul_congr_below e (chainHilbertSeries N n)
    (truncatedChainSeries N n (e 0) Finset.univ) _ (fun d hd =>
      coeff_chainHilbertSeries_truncated N n (e 0) d (hd 0))]
  rw [denominator_mul_truncatedChainSeries,
    coeff_truncation_correction n (e 0) Finset.univ e _ le_rfl]

/-- Short-range cycle counting, with its polynomial denominator cleared. -/
theorem cycleHilbertSeries_product (N n : ℕ) (hn : n ≤ N) :
    (∏ i : Fin (n + 1), (1 - evenGeneratorSeries i.val)) *
      cycleHilbertSeries N (n + 1) =
      ∏ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (1 + oddGeneratorSeries (N + 1) i.val) := by
  classical
  ext e
  rw [coeff_mul_congr_below e (cycleHilbertSeries N (n + 1))
    (truncatedChainSeries (N + 1) (n + 1) (e 0) (Finset.univ.erase 0)) _
    (fun d hd => coeff_cycleHilbertSeries_truncated N n (e 0) hn d (hd 0))]
  rw [denominator_mul_truncatedChainSeries,
    coeff_truncation_correction (n + 1) (e 0) Finset.univ e _ le_rfl]


theorem evenGeneratorSeries_product (n : ℕ) :
    (∏ i : Fin n, (1 - evenGeneratorSeries i.val)) =
      qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n := by
  simp_rw [evenGeneratorSeries_eq]
  exact Fin.prod_univ_eq_prod_range
    (fun i => (1 - (MvPowerSeries.X 0 : Series) * MvPowerSeries.X 1 ^ i)) n

theorem oddGeneratorSeries_product (N n : ℕ) :
    (∏ i : Fin n, (1 + oddGeneratorSeries N i.val)) =
      qPochhammer (-(MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ N)
        (MvPowerSeries.X 1) n := by
  simp_rw [oddGeneratorSeries_eq]
  unfold qPochhammer
  simp only [neg_mul, sub_neg_eq_add]
  exact Fin.prod_univ_eq_prod_range
    (fun i => (1 + (MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ N * MvPowerSeries.X 1 ^ i)) n

theorem oddGeneratorSeries_product_erase (N n : ℕ) :
    (∏ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (1 + oddGeneratorSeries N i.val)) =
      ∏ j ∈ Finset.Ico 1 (n + 1),
        (1 + (MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ N * MvPowerSeries.X 1 ^ j) := by
  classical
  simp_rw [oddGeneratorSeries_eq]
  apply Finset.prod_bij (fun i _ => i.val)
  · intro i hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    have hv : i.val ≠ 0 := by intro h; apply hi0; exact Fin.ext h
    exact Finset.mem_Ico.mpr ⟨by omega, i.isLt⟩
  · intro i hi j hj he
    exact Fin.ext he
  · intro j hj
    have hj' := Finset.mem_Ico.mp hj
    refine ⟨⟨j, hj'.2⟩, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_zero] at hh
    omega
  · intro i hi
    rfl

/-- The initial identity for the actual Hilbert numerator, at every short length.
The formula is multiplied by z and hence needs no inverse of that variable. -/
theorem hilbertSeries_initial_identity (N n : ℕ) (hn : 1 ≤ n) (hshort : n ≤ N + 1) :
    (MvPowerSeries.X 2 : Series) *
        (qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n * hilbertSeries N n) =
      (1 + MvPowerSeries.X 2) *
        (∏ j ∈ Finset.Ico 1 n,
          (1 + (MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ (N + 1) * MvPowerSeries.X 1 ^ j)) -
      qPochhammer (-(MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ N)
        (MvPowerSeries.X 1) n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm : m ≤ N := by omega
  rw [← evenGeneratorSeries_product]
  calc
    _ = (∏ i : Fin (m + 1), (1 - evenGeneratorSeries i.val)) *
        ((MvPowerSeries.X 2 : Series) * hilbertSeries N (m + 1)) := by ring
    _ = (1 + MvPowerSeries.X 2) *
        ((∏ i : Fin (m + 1), (1 - evenGeneratorSeries i.val)) * cycleHilbertSeries N (m + 1)) -
        (∏ i : Fin (m + 1), (1 - evenGeneratorSeries i.val)) * chainHilbertSeries N (m + 1) := by
      rw [hilbertSeries_from_chains_and_cycles]
      ring
    _ = _ := by
      rw [cycleHilbertSeries_product N m hm, chainHilbertSeries_product,
        oddGeneratorSeries_product, oddGeneratorSeries_product_erase]


theorem shortRangeCycleProduct_eq (N n : ℕ) :
    (∏ j ∈ Finset.Ico 1 (n + 1),
      (1 + (MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ (N + 1) * MvPowerSeries.X 1 ^ j)) =
    qPochhammer (-(MvPowerSeries.X 2 : Series) * MvPowerSeries.X 0 ^ (N + 1) *
      MvPowerSeries.X 1) (MvPowerSeries.X 1) n := by
  rw [Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel, qPochhammer]
  apply Finset.prod_congr rfl
  intro i hi
  rw [pow_add]
  ring

/-- The finite formula is proved at every positive short length, including N+1. -/
theorem finite_hilbert_series_shortRange (N n : ℕ) (hN : 0 < N) (hn : n ≤ N) :
    qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) (n + 1) *
      hilbertSeries N (n + 1) = finiteNumerator N (n + 1) := by
  have hleft := hilbertSeries_initial_identity N (n + 1) (by omega) (by omega)
  rw [shortRangeCycleProduct_eq, ← finiteNumerator_initial N n hN hn] at hleft
  ext e
  have he := congrArg (MvPowerSeries.coeff (Finsupp.single (2 : Fin 3) 1 + e)) hleft
  simpa only [MvPowerSeries.X, MvPowerSeries.coeff_add_monomial_mul, one_mul] using he

end TorusLinkHomology.HilbertSeries
