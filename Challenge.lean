import DGA.Exterior
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
Standalone challenges for DGA homology generation and Theorems A.4/A.5.
Only DGA and mathlib are imported. The torus-link definitions are local;
the three main proofs are intentionally left as `sorry`.
The Hilbert-series section is copied verbatim from the archived original.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology

abbrev R (n : ℕ) := MvPolynomial (Fin n) ℚ
abbrev V (n : ℕ) := Fin n →₀ R n
abbrev A (n : ℕ) := ExteriorAlgebra (R n) (V n)

def u (n : ℕ) (i : Fin n) : R n := MvPolynomial.X i

def uPolynomial (n : ℕ) : Polynomial (R n) :=
  ∑ i : Fin n, Polynomial.monomial i.val (u n i)

def differentialCoefficient (N n : ℕ) (i : Fin n) : R n :=
  ((uPolynomial n) ^ N).coeff i.val

def xi (n : ℕ) (i : Fin n) : A n :=
  ExteriorAlgebra.ι (R n) (Finsupp.single i 1)

def differentialFunctional (N n : ℕ) : V n →ₗ[R n] R n :=
  Finsupp.linearCombination (R n) (differentialCoefficient N n)

def mu (N n k : ℕ) : A n :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i.val + j.val = k then
      (((N : R n) * (i.val : R n) - (j.val : R n)) * u n i) • xi n j
    else 0

/-- The coefficient Koszul DGA, using the generic DGA infrastructure. -/
def torusLinkDGA (N n : ℕ) : DGA (R n) (A n) :=
  ExteriorAlgebra.koszulDGA (R n) (V n) (differentialFunctional N n)

abbrev Homology (N n : ℕ) := (torusLinkDGA N n).Homology

/-- The named elements μ₁,…,μₙ₋₁ are cycles whose classes generate the
DGA homology as an algebra over R n. The cycle representatives are bundled
with generation so that no separate admitted cycle lemma is needed. -/
theorem homology_generated_by_mu (n N : ℕ) (hN : 0 < N) :
    ∃ c : {k : ℕ // 1 ≤ k ∧ k < n} → (torusLinkDGA N n).cycles,
      (∀ k, (c k : A n) = mu N n k.val) ∧
      Algebra.adjoin (R n)
        (Set.range fun k => (torusLinkDGA N n).homologyClass (c k)) = ⊤ := by
  sorry

namespace CoordinateKoszul

def chainBasis (n : ℕ) : Module.Basis (Finset (Fin n)) (R n) (A n) :=
  (Finsupp.basisSingleOne : Module.Basis (Fin n) (R n) (V n)).ExteriorAlgebra

def rationalChainBasis (n : ℕ) :
    Module.Basis ((Fin n →₀ ℕ) × Finset (Fin n)) ℚ (A n) :=
  (MvPolynomial.basisMonomials (Fin n) ℚ).smulTower (chainBasis n)

end CoordinateKoszul
end TorusLinkHomology

namespace TorusLinkHomology.HilbertSeries

open CoordinateKoszul

/-- A finite indexing type for monomials in the n polynomial generators
u₀,…,uₙ₋₁ and n exterior generators ξ₀,…,ξₙ₋₁. Each polynomial exponent
is at most a; the exterior monomial is indexed by a subset of Fin n.
The total polynomial degree is not constrained here. -/
abbrev BoundedMonomial (n a : ℕ) := (Fin n → Fin (a + 1)) × Finset (Fin n)

/-- The actual monomial in the existing coefficient Koszul algebra. -/
def chainMonomial (n a : ℕ) (m : BoundedMonomial n a) : A n :=
  rationalChainBasis n
    (Finsupp.equivFunOnFinite.symm (fun i => (m.1 i).val), m.2)

/-- The three degree constraints on a monomial u^m ξ_I. -/
def HasDegree (N n a b h : ℕ) (m : BoundedMonomial n a) : Prop :=
  (∑ i : Fin n, (m.1 i).val) + N * m.2.card = a ∧
    (∑ i : Fin n, i.val * (m.1 i).val) + (∑ i ∈ m.2, i.val) = b ∧
    m.2.card = h

/-- The rational homogeneous chain space in degree (a,b,h).
The bound on each exponent loses no monomials: their sum is at most a. -/
def chainPiece (N n a b h : ℕ) : Submodule ℚ (A n) :=
  Submodule.span ℚ (Set.range fun m : {m : BoundedMonomial n a // HasDegree N n a b h m} =>
    chainMonomial n a m.val)

instance chainPiece_finiteDimensional (N n a b h : ℕ) :
    FiniteDimensional ℚ (chainPiece N n a b h) := by
  unfold chainPiece
  exact FiniteDimensional.span_of_finite ℚ (Set.finite_range _)

/-- Homogeneous cycles, as a subspace of the existing cycle algebra. -/
def cyclePiece (N n a b h : ℕ) : Submodule ℚ (torusLinkDGA N n).cycles :=
  (chainPiece N n a b h).comap
    ((torusLinkDGA N n).cycles.val.toLinearMap.restrictScalars ℚ)

instance cyclePiece_finiteDimensional (N n a b h : ℕ) :
    FiniteDimensional ℚ (cyclePiece N n a b h) := by
  let inclusion : cyclePiece N n a b h →ₗ[ℚ] chainPiece N n a b h :=
    { toFun := fun x => ⟨(x.val : A n), x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective inclusion
  intro x y hxy
  have hval : (x.val : A n) = (y.val : A n) :=
    congrArg (fun z : chainPiece N n a b h => (z : A n)) hxy
  exact Subtype.ext (Subtype.ext hval)

/-- The homogeneous homology piece, inside the actual total homology algebra. -/
def homologyPiece (N n a b h : ℕ) : Submodule ℚ (Homology N n) :=
  (cyclePiece N n a b h).map
    ((torusLinkDGA N n).homologyClass.toLinearMap.restrictScalars ℚ)

instance homologyPiece_finiteDimensional (N n a b h : ℕ) :
    FiniteDimensional ℚ (homologyPiece N n a b h) := by
  unfold homologyPiece
  infer_instance

/-- The actual finite dimension of H_h(K_n) in polynomial degree a and weight b. -/
def homologyDimension (N n a b h : ℕ) : ℕ :=
  Module.finrank ℚ (homologyPiece N n a b h)

/-- Formal series in coordinates 0 = s, 1 = v, 2 = z. -/
abbrev Series := MvPowerSeries (Fin 3) ℚ

/-- The trigraded Hilbert series of the existing Koszul homology. -/
def hilbertSeries (N n : ℕ) : Series :=
  fun e => (homologyDimension N n (e 0) (e 1) (e 2) : ℚ)

/-- Finite q-Pochhammer product (a;v)_m. -/
def qPochhammer {S : Type*} [CommRing S] (a v : S) (m : ℕ) : S :=
  ∏ j ∈ Finset.range m, (1 - a * v ^ j)

/-- Gaussian binomial polynomial, extended by zero when the lower index
exceeds the upper index. The recursion avoids division by nonunits. -/
def gaussianBinomial {S : Type*} [CommRing S] (v : S) : ℕ → ℕ → S
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | a + 1, b + 1 => gaussianBinomial v a (b + 1) + v ^ (a - b) * gaussianBinomial v a b

/-- The numerator corrections δ_j in Theorem A.4 (only j ≤ N is used). -/
def numeratorCorrection {S : Type*} [CommRing S] (N : ℕ) (s v z : S) : ℕ → S
  | 0 => 1
  | 1 => -(s ^ N * (1 + z * s))
  | j + 2 => -((1 - s) * s ^ N * v ^ (j + 1) * qPochhammer (-z * s ^ N) v (j + 1))

/-- E_i = ((2N+1)i²-i)/2. The numerator is nonnegative and even. -/
def quadraticExponent (N i : ℕ) : ℕ := ((2 * N + 1) * i ^ 2 - i) / 2

/-- The explicit finite sum in Theorem A.4, interpreted as a formal series. -/
def finiteNumerator (N n : ℕ) : Series :=
  let s : Series := MvPowerSeries.X 0
  let v : Series := MvPowerSeries.X 1
  let z : Series := MvPowerSeries.X 2
  ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (N + 1),
    if (N + 1) * i + j ≤ n then
      (-1) ^ i * s ^ (N * i) * v ^ (quadraticExponent N i + i * j) *
        qPochhammer s v i * qPochhammer (-z * s ^ N) v (N * i) *
        numeratorCorrection N (s * v ^ i) v z j *
        qPochhammer (-z * s ^ (N + 1) * v ^ ((N + 1) * i + j)) v
          (n - ((N + 1) * i + j)) * gaussianBinomial v (n - N * i - j) i
    else 0

/-- Theorem A.4, algebraic form, including the empty complex n = 0.
Multiplication by (s;v)_n clears the denominator; the right-hand side is a
finite polynomial expression. No rationality assumption on the left is made. -/
theorem finite_hilbert_series (N n : ℕ) (hN : 0 < N) :
    qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) n *
      hilbertSeries N n = finiteNumerator N n := by
  sorry

/-- Formal charge series in coordinates 0 = y, 1 = v. -/
abbrev ChargeSeries := MvPowerSeries (Fin 2) ℚ

/-- Decreasing sequences n₁ ≥ ... ≥ n_{N-1} ≥ 0 of sum k.
The final n_N = 0 is supplied explicitly in `gordonCoefficient`.
Every entry is bounded by k, making the indexing type finite. -/
def GordonAdmissible (N k : ℕ) (m : Fin (N - 1) → Fin (k + 1)) : Prop :=
  Antitone (fun j => (m j).val) ∧ (∑ j : Fin (N - 1), (m j).val) = k

/-- The Gordon sum g_{N,i;k}(v), embedded in series in (y,v).
Only 1 ≤ i ≤ N is used. Denominators have constant coefficient one, so the
inverses are genuine formal power-series inverses. -/
def gordonCoefficient (N i k : ℕ) : ChargeSeries := by
  classical
  let v : ChargeSeries := MvPowerSeries.X 1
  exact ∑ m : {m : Fin (N - 1) → Fin (k + 1) // GordonAdmissible N k m},
    let value : ℕ → ℕ := fun j => if hj : j < N - 1 then (m.val ⟨j, hj⟩).val else 0
    v ^ ((∑ j ∈ Finset.range (N - 1), value j * (value j - 1)) +
        ∑ j ∈ Finset.Ico (i - 1) (N - 1), value j) *
      (∏ j ∈ Finset.range (N - 1), qPochhammer v v (value j - value (j + 1)))⁻¹

/-- The positive coefficient c_{N,k}(y,v) asserted by Theorem A.5. -/
def fermionicCoefficient (N k : ℕ) : ChargeSeries :=
  let y : ChargeSeries := MvPowerSeries.X 0
  let v : ChargeSeries := MvPowerSeries.X 1
  if k < N - 1 then
    qPochhammer (-y * v) v k * (qPochhammer v v k)⁻¹
  else
    qPochhammer (-y) v (k + 1 - N) * gordonCoefficient N N k +
      y * ∑ i ∈ Finset.Ico 1 N,
        v ^ (k - i) * qPochhammer (-y) v (k - i) * gordonCoefficient N i k

/-- Theorem A.5, algebraic coefficient form.
For weight b, every length n > b already gives the infinite-strand answer.
The coefficient of y^h v^b has polynomial degree a = k + N*h. Thus this
statement includes stabilization and counts the actual finite-stage homology,
rather than defining a putative Hilbert series by the proposed formula. -/
theorem stable_homology_coefficient (N : ℕ) (hN : 0 < N) (k b h n : ℕ)
    (hn : b < n) :
    (homologyDimension N n (k + N * h) b h : ℚ) =
      MvPowerSeries.coeff (Finsupp.single 0 h + Finsupp.single 1 b)
        (fermionicCoefficient N k) := by
  sorry

/-- The stable charge series, defined independently from homology dimensions
at the sufficient finite length b+1 for each coefficient of weight b. -/
def stableChargeSeries (N k : ℕ) : ChargeSeries :=
  fun e => (homologyDimension N (e 1 + 1) (k + N * e 0) (e 1) (e 0) : ℚ)

/-- The power-series formulation of Theorem A.5 follows from its coefficient
form, without any additional admission or direct-limit machinery. -/
theorem stable_charge_series (N : ℕ) (hN : 0 < N) (k : ℕ) :
    stableChargeSeries N k = fermionicCoefficient N k := by
  ext e
  have he : Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) = e := by
    ext i
    fin_cases i <;> simp
  simpa only [MvPowerSeries.coeff_apply, stableChargeSeries, he] using
    stable_homology_coefficient N hN k (e 1) (e 0) (e 1 + 1) (Nat.lt_succ_self _)

/-- The integrality and nonnegativity conclusion of Theorem A.5: every
coefficient is a natural-number dimension. -/
theorem fermionicCoefficient_coeff_nat (N : ℕ) (hN : 0 < N) (k : ℕ)
    (e : Fin 2 →₀ ℕ) :
    ∃ d : ℕ, MvPowerSeries.coeff e (fermionicCoefficient N k) = (d : ℚ) := by
  rw [← stable_charge_series N hN k]
  exact ⟨homologyDimension N (e 1 + 1) (k + N * e 0) (e 1) (e 0), rfl⟩

end TorusLinkHomology.HilbertSeries
