import TorusLinkHomology.HilbertSeries.ChargeTransform
import TorusLinkHomology.HilbertSeries.FiniteRecurrence

/-! The finite numerator in nonnegative charge coordinates. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

@[simp] theorem chargeEmbedding_X_zero (N : ℕ) :
    chargeEmbedding N (MvPowerSeries.X 0) = MvPowerSeries.X 0 := by
  exact MvPowerSeries.substAlgHom_X (chargeVariables_hasSubst N) 0

@[simp] theorem chargeEmbedding_X_one (N : ℕ) :
    chargeEmbedding N (MvPowerSeries.X 1) = MvPowerSeries.X 1 := by
  exact MvPowerSeries.substAlgHom_X (chargeVariables_hasSubst N) 1

@[simp] theorem chargeEmbedding_X_two (N : ℕ) :
    chargeEmbedding N (MvPowerSeries.X 2) = MvPowerSeries.X 0 ^ N * MvPowerSeries.X 2 := by
  exact MvPowerSeries.substAlgHom_X (chargeVariables_hasSubst N) 2

/-- The numerator correction after introducing y=z*s^N. -/
def chargedCorrection {S : Type*} [CommRing S] (N : ℕ) (s v y : S) : ℕ → S
  | 0 => 1
  | 1 => -(s ^ N + y * s)
  | j + 2 => -((1 - s) * s ^ N * v ^ (j + 1) * qPochhammer (-y) v (j + 1))

theorem map_chargedCorrection {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (N : ℕ) (s v y : S) (j : ℕ) :
    f (chargedCorrection N s v y j) = chargedCorrection N (f s) (f v) (f y) j := by
  cases j with
  | zero => simp [chargedCorrection]
  | succ j => cases j <;> simp [chargedCorrection, map_qPochhammer]

theorem chargedCorrection_substitution {S : Type*} [CommRing S]
    (N : ℕ) (s v z : S) (j : ℕ) :
    chargedCorrection N s v (s ^ N * z) j = numeratorCorrection N s v z j := by
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero => simp only [chargedCorrection, numeratorCorrection]; ring
    | succ j => simp only [chargedCorrection, numeratorCorrection, mul_comm (s ^ N) z, neg_mul]

theorem chargeEmbedding_qPochhammer (N : ℕ) (a v : Series) (m : ℕ) :
    chargeEmbedding N (qPochhammer a v m) =
      qPochhammer (chargeEmbedding N a) (chargeEmbedding N v) m :=
  map_qPochhammer (chargeEmbedding N).toRingHom a v m

theorem chargeEmbedding_gaussianBinomial (N : ℕ) (v : Series) (n k : ℕ) :
    chargeEmbedding N (gaussianBinomial v n k) = gaussianBinomial (chargeEmbedding N v) n k :=
  map_gaussianBinomial (chargeEmbedding N).toRingHom v n k

theorem chargeEmbedding_chargedCorrection (N : ℕ) (s v y : Series) (j : ℕ) :
    chargeEmbedding N (chargedCorrection N s v y j) =
      chargedCorrection N (chargeEmbedding N s) (chargeEmbedding N v) (chargeEmbedding N y) j :=
  map_chargedCorrection (chargeEmbedding N).toRingHom N s v y j

def chargedFiniteNumerator (N n : ℕ) : Series :=
  let s : Series := MvPowerSeries.X 0
  let v : Series := MvPowerSeries.X 1
  let y : Series := MvPowerSeries.X 2
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (N + 1),
    if (N + 1) * i + j ≤ n then
      (-1) ^ i * s ^ (N * i) * v ^ (quadraticExponent N i + i * j) *
        qPochhammer s v i * qPochhammer (-y) v (N * i) *
        chargedCorrection N (s * v ^ i) v (y * v ^ (N * i)) j *
        qPochhammer (-y * s * v ^ ((N + 1) * i + j)) v
          (n - ((N + 1) * i + j)) * gaussianBinomial v (n - N * i - j) i
    else 0

/-- The charge-normalized polynomial is sent to exactly the original numerator. -/
theorem chargeEmbedding_chargedFiniteNumerator (N n : ℕ) :
    chargeEmbedding N (chargedFiniteNumerator N n) = finiteNumerator N n := by
  classical
  unfold chargedFiniteNumerator finiteNumerator
  simp only [map_sum, apply_ite, map_zero, map_mul, map_pow, map_neg, map_one,
    chargeEmbedding_X_zero, chargeEmbedding_X_one, chargeEmbedding_X_two,
    chargeEmbedding_qPochhammer, chargeEmbedding_chargedCorrection, chargeEmbedding_gaussianBinomial]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with hij
  · have hc : (MvPowerSeries.X 0 : Series) ^ N * MvPowerSeries.X 2 * MvPowerSeries.X 1 ^ (N * i) =
        (MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ i) ^ N * MvPowerSeries.X 2 := by
      rw [mul_pow, ← pow_mul]
      rw [Nat.mul_comm i N]
      ring
    have ht : (-(MvPowerSeries.X 0 ^ N * MvPowerSeries.X 2) * MvPowerSeries.X 0 : Series) =
        -MvPowerSeries.X 2 * MvPowerSeries.X 0 ^ (N + 1) := by rw [pow_succ]; ring
    rw [hc, chargedCorrection_substitution, ht]
    have hp : (-(MvPowerSeries.X 0 ^ N * MvPowerSeries.X 2) : Series) =
        -MvPowerSeries.X 2 * MvPowerSeries.X 0 ^ N := by ring
    rw [hp]
  · rfl

/-- Transforming the finite formula uses the injective positive substitution,
so no inverse of the variable s is introduced. -/
theorem chargedFiniteFormula_of_finite (N n : ℕ)
    (hfinite : qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n *
      hilbertSeries N n = finiteNumerator N n) :
    qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n *
      chargeTransform N (hilbertSeries N n) = chargedFiniteNumerator N n := by
  apply chargeEmbedding_injective N
  rw [map_mul, chargeEmbedding_qPochhammer, chargeEmbedding_X_zero, chargeEmbedding_X_one,
    chargeEmbedding_hilbertSeries, chargeEmbedding_chargedFiniteNumerator]
  exact hfinite

end TorusLinkHomology.HilbertSeries
