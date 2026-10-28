import TorusLinkHomology.Homology
import TorusLinkHomology.Generation.CoordinateContraction
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Algebraic Hilbert-series statements for coefficient Koszul homology

Definitions for the algebraic content of Theorems A.4 and A.5 of `proof/GOR.tex`.
All homogeneous pieces refer to the existing Koszul differential and total
homology, and their finite-dimensionality is proved.
No topological link homology or Rasmussen spectral sequence is defined here.

The grading is deg(uᵢ) = (1,i,0), deg(ξᵢ) = (N,i,1). Homogeneous homology
pieces are images of homogeneous cycles in `TorusLinkHomology.Homology`.
Three-variable series use coordinates (s,v,z); two-variable charge series use
(y,v). All series have rational coefficients, with dimensions cast from ℕ.

The infinite-strand statement is made coefficientwise, at every finite length
n > b in weight b. This includes stabilization, without assuming a direct-limit
construction or substituting a negative power of s into a formal power series.
-/

noncomputable section

open scoped BigOperators

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

/-- The stable charge series, defined independently from homology dimensions
at the sufficient finite length b+1 for each coefficient of weight b. -/
def stableChargeSeries (N k : ℕ) : ChargeSeries :=
  fun e => (homologyDimension N (e 1 + 1) (k + N * e 0) (e 1) (e 0) : ℚ)


end TorusLinkHomology.HilbertSeries
