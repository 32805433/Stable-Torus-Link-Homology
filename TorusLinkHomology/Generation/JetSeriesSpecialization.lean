import TorusLinkHomology.Generation.UniversalJetEvaluation
import TorusLinkHomology.Generation.UniversalIdentity
import TorusLinkHomology.Generation.EulerLeibniz
import TorusLinkHomology.Generation.SelectorCoefficient

/-!
# Specialization of the finite universal jets into coefficient series

Divided jet coordinates turn the universal differential coefficients into
divided Euler derivatives of the actual power. The exterior substitution
preserves the order of every odd product.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.UniversalJets

variable {S M : Type*} [CommRing S] [Algebra ℚ S] [AddCommGroup M] [Module S M]

open CoefficientSeries

/-- The finite coefficient polynomial specializes to the truncated Euler jet. -/
theorem evenJetMap_uPolynomial (n : ℕ) (b : ℤ) (U : PowerSeries S) :
    (uPolynomial n).map (evenJetMap n b U) = jetPolynomial n b U := by
  simp only [uPolynomial, Polynomial.map_sum, Polynomial.map_monomial, u,
    evenJetMap_X, jetPolynomial]

/-- The universal differential specializes to the divided derivative of the
power, exactly below the available finite jet cutoff. -/
theorem evenJetMap_differentialCoefficient (N n : ℕ) (b : ℤ) (U : PowerSeries S)
    (j : Fin n) :
    evenJetMap n b U (differentialCoefficient N n j) =
      hasseEuler ((N : ℤ) * b) j.val (U ^ N) := by
  rw [differentialCoefficient, ← Polynomial.coeff_map, Polynomial.map_pow,
    evenJetMap_uPolynomial, coeff_jetPolynomial_pow_of_lt n N b U j.val j.isLt]

/-- Ordinary even jets become ordinary Euler iterates. -/
theorem evenJetMap_evenJet (n : ℕ) (b : ℤ) (U : PowerSeries S) (j : Fin n) :
    evenJetMap n b U (evenJet n j) = (shiftedEuler b)^[j.val] U := by
  simp only [evenJet, map_mul, map_natCast, u, evenJetMap_X,
    factorial_mul_hasseEuler]

/-- Cancelling the divided-jet factorial identifies the coefficient of the
shifted polynomial `X^i p`. -/
theorem jetCoefficient_mul_dividedPower (p : Polynomial ℚ) (i j : ℕ) (x : ℚ) :
    jetCoefficient p i j * (x ^ j / (j.factorial : ℚ)) =
      (Polynomial.X ^ i * p).coeff j * x ^ j := by
  rw [jetCoefficient, Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · field_simp
  · simp

/-- The finite selector-jet sum is exactly the indicated Euler iterate;
the degree bound guarantees that no polynomial coefficient is truncated. -/
theorem sum_jetCoefficient_hasseEuler {E : Type*} [Ring E] [Algebra ℚ E]
    (N i : ℕ) (p : Polynomial ℚ) (hp : p.natDegree + i ≤ N)
    (b : ℤ) (f : PowerSeries E) :
    (∑ j : Fin (N + 1), jetCoefficient p i j.val • hasseEuler b j.val f) =
      (shiftedEuler b)^[i] (evalEuler p b f) := by
  ext t : 1
  simp only [map_sum, PowerSeries.coeff_smul, coeff_hasseEuler, smul_smul,
    coeff_iterate_shiftedEuler, coeff_evalEuler]
  rw [← Finset.sum_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, smul_smul]
  congr 1
  simp_rw [jetCoefficient_mul_dividedPower]
  let G : ℕ → ℚ := fun j => (Polynomial.X ^ i * p).coeff j *
    (((b - (t : ℤ) : ℤ) : ℚ) ^ j)
  change (∑ j : Fin (N + 1), G j.val) = _
  rw [Fin.sum_univ_eq_sum_range G]
  dsimp only [G]
  have hdegree : (Polynomial.X ^ i * p).natDegree < N + 1 := by
    have h : (Polynomial.X ^ i * p).natDegree ≤
        (Polynomial.X ^ i : Polynomial ℚ).natDegree + p.natDegree :=
      Polynomial.natDegree_mul_le
    simp only [Polynomial.natDegree_X_pow] at h
    omega
  rw [← Polynomial.eval_eq_sum_range' hdegree]
  simp

local instance : Algebra ℚ (ExteriorAlgebra S M) :=
  Algebra.compHom (ExteriorAlgebra S M) (algebraMap ℚ S)

/-- Module coefficients for the divided jet of an odd series. -/
def oddJetCoefficients (b : ℤ) (j : ℕ) (C : ℕ → M) (t : ℕ) : M :=
  algebraMap ℚ S ((((b - (t : ℤ) : ℤ) : ℚ) ^ j) / (j.factorial : ℚ)) • C t

/-- The divided odd jet is still a series of degree-one exterior elements. -/
theorem iotaSeries_oddJetCoefficients (b : ℤ) (j : ℕ) (C : ℕ → M) :
    ExteriorAlgebra.iotaSeries (R := S) (oddJetCoefficients (S := S) b j C) =
      hasseEuler b j (ExteriorAlgebra.iotaSeries (R := S) C) := by
  ext t : 1
  simp only [ExteriorAlgebra.coeff_iotaSeries, oddJetCoefficients, map_smul,
    coeff_hasseEuler]
  rfl

/-- Universal finite jet substitution into ordinary coefficient series. -/
def seriesJetMap (n : ℕ) (b c : ℤ) (U : PowerSeries S) (C : ℕ → M) :
    A n →+* PowerSeries (ExteriorAlgebra S M) :=
  ExteriorAlgebra.seriesLift (evenJetMap n b U) (fun j => oddJetCoefficients (S := S) c j.val C)

@[simp] theorem seriesJetMap_xi (n : ℕ) (b c : ℤ) (U : PowerSeries S)
    (C : ℕ → M) (j : Fin n) :
    seriesJetMap n b c U C (xi n j) =
      hasseEuler c j.val (ExteriorAlgebra.iotaSeries (R := S) C) := by
  rw [seriesJetMap, xi, ExteriorAlgebra.seriesLift_single, iotaSeries_oddJetCoefficients]

@[simp] theorem seriesJetMap_algebraMap (n : ℕ) (b c : ℤ) (U : PowerSeries S)
    (C : ℕ → M) (a : R n) :
    seriesJetMap n b c U C (algebraMap (R n) (A n) a) =
      PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) (evenJetMap n b U a) := by
  exact ExteriorAlgebra.seriesLift_algebraMap (evenJetMap n b U)
    (fun j : Fin n => oddJetCoefficients (S := S) c j.val C) a

/-- Scalar multiplication specializes to multiplication by a central series. -/
theorem seriesJetMap_smul (n : ℕ) (b c : ℤ) (U : PowerSeries S)
    (C : ℕ → M) (a : R n) (x : A n) :
    seriesJetMap n b c U C (a • x) =
      PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) (evenJetMap n b U a) *
        seriesJetMap n b c U C x := by
  rw [Algebra.smul_def, map_mul, seriesJetMap_algebraMap]

/-- Ordinary odd jets become ordinary Euler iterates. -/
theorem seriesJetMap_oddJet (n : ℕ) (b c : ℤ) (U : PowerSeries S)
    (C : ℕ → M) (j : Fin n) :
    seriesJetMap n b c U C (oddJet n j) =
      (shiftedEuler c)^[j.val] (ExteriorAlgebra.iotaSeries (R := S) C) := by
  rw [oddJet, seriesJetMap_smul, map_natCast, map_natCast, seriesJetMap_xi,
    factorial_mul_hasseEuler]

/-- Rational scalar multiplication is preserved by the series substitution. -/
theorem seriesJetMap_rat_smul (n : ℕ) (b c : ℤ) (U : PowerSeries S)
    (C : ℕ → M) (a : ℚ) (x : A n) :
    seriesJetMap n b c U C (algebraMap ℚ (R n) a • x) =
      a • seriesJetMap n b c U C x := by
  rw [seriesJetMap_smul]
  change PowerSeries.map (algebraMap S (ExteriorAlgebra S M))
    (evenJetMap n b U (MvPolynomial.C a)) * _ = _
  rw [evenJetMap_C]
  simp only [PowerSeries.algebraMap_apply, PowerSeries.map_C, Algebra.smul_def,
    Algebra.compHom_algebraMap_apply]

/-- A finite universal selector vector becomes `D^i p(D)C`. -/
theorem seriesJetMap_jetVector (N i : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree + i ≤ N) (b c : ℤ) (U : PowerSeries S) (C : ℕ → M) :
    seriesJetMap (N + 1) b c U C
      (ExteriorAlgebra.ι (R (N + 1)) (jetVector N p i)) =
      (shiftedEuler c)^[i] (evalEuler p c (ExteriorAlgebra.iotaSeries (R := S) C)) := by
  simp only [jetVector, map_sum, map_smul]
  change (∑ j : Fin (N + 1), seriesJetMap (N + 1) b c U C
    (algebraMap ℚ (R (N + 1)) (jetCoefficient p i j.val) • xi (N + 1) j)) = _
  simp only [seriesJetMap_rat_smul, seriesJetMap_xi]
  exact sum_jetCoefficient_hasseEuler N i p hp c _

/-- The even selector expression specializes without losing a jet. -/
theorem evenJetMap_jetDifferential (N i : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree + i ≤ N) (b : ℤ) (U : PowerSeries S) :
    evenJetMap (N + 1) b U (jetDifferential N p i) =
      (shiftedEuler ((N : ℤ) * b))^[i] (evalEuler p ((N : ℤ) * b) (U ^ N)) := by
  simp only [jetDifferential, map_sum, map_mul, evenJetMap_differentialCoefficient,
    MvPolynomial.algebraMap_eq, evenJetMap_C]
  change (∑ j : Fin (N + 1), algebraMap ℚ (PowerSeries S) (jetCoefficient p i j.val) *
    hasseEuler ((N : ℤ) * b) j.val (U ^ N)) = _
  simp_rw [← Algebra.smul_def]
  exact sum_jetCoefficient_hasseEuler N i p hp _ _

/-- Scalar extension commutes with divided Euler jets. -/
theorem map_hasseEuler_scalar (b : ℤ) (i : ℕ) (f : PowerSeries S) :
    PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) (hasseEuler b i f) =
      hasseEuler b i (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) f) := by
  ext t : 1
  simp only [PowerSeries.coeff_map, coeff_hasseEuler, Algebra.smul_def, map_mul,
    Algebra.compHom_algebraMap_apply]

omit [Algebra ℚ S] in
/-- Scalar extension commutes with ordinary Euler iterates. -/
theorem map_iterate_shiftedEuler_scalar (b : ℤ) (i : ℕ) (f : PowerSeries S) :
    PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) ((shiftedEuler b)^[i] f) =
      (shiftedEuler b)^[i] (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) f) := by
  ext t : 1
  simp only [PowerSeries.coeff_map, coeff_iterate_shiftedEuler, map_zsmul]

/-- Scalar extension commutes with a rational polynomial in Euler. -/
theorem map_evalEuler_scalar (p : Polynomial ℚ) (b : ℤ) (f : PowerSeries S) :
    PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) (evalEuler p b f) =
      evalEuler p b (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) f) := by
  ext t : 1
  simp only [PowerSeries.coeff_map, coeff_evalEuler, Algebra.smul_def, map_mul,
    Algebra.compHom_algebraMap_apply]

/-- Evaluating the scalar-extended polynomial is the same rational Euler
operator on the exterior series. -/
theorem evalEuler_map_scalar (p : Polynomial ℚ) (b : ℤ)
    (f : PowerSeries (ExteriorAlgebra S M)) :
    evalEuler (p.map (algebraMap ℚ S)) b f = evalEuler p b f := by
  ext t : 1
  rw [coeff_evalEuler, coeff_evalEuler]
  have hcast : ((b - (t : ℤ) : ℤ) : S) =
      algebraMap ℚ S (((b - (t : ℤ) : ℤ) : ℚ)) := by simp
  rw [hcast, Polynomial.eval_map_apply]
  rfl

/-- Exterior multiplication is evaluated in the original factor order. -/
theorem seriesJetMap_iotaMulti (n q : ℕ) (b c : ℤ) (U : PowerSeries S)
    (C : ℕ → M) (v : Fin q → V n) :
    seriesJetMap n b c U C (ExteriorAlgebra.ιMulti (R n) q v) =
      (List.ofFn (fun j => seriesJetMap n b c U C (ExteriorAlgebra.ι (R n) (v j)))).prod := by
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, Function.comp_def]

/-- The entire finite universal selector cycle specializes to the actual
Euler deletion expression, with both upper exponent bounds explicit. -/
theorem seriesJetMap_selectorCycle (N q : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree + q ≤ N) (b c : ℤ) (U : PowerSeries S) (C : ℕ → M) :
    seriesJetMap (N + 1) b c U C (selectorCycle N q p) =
      CoefficientSelector.eulerDeletionSeries q p c ((N : ℤ) * b)
        (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) (U ^ N))
        (ExteriorAlgebra.iotaSeries (R := S) C) := by
  simp only [selectorCycle, map_sum, seriesJetMap_smul,
    CoefficientSelector.eulerDeletionSeries, evalEuler_map_scalar]
  apply Finset.sum_congr rfl
  intro a _
  have ha : p.natDegree + a.val ≤ N := by have := a.isLt; omega
  rw [map_mul, map_pow, map_neg, map_one, map_mul, map_pow, map_neg, map_one,
    evenJetMap_jetDifferential N a.val p ha, map_iterate_shiftedEuler_scalar,
    map_evalEuler_scalar, seriesJetMap_iotaMulti]
  have hprod : (List.ofFn (fun j : Fin q => seriesJetMap (N + 1) b c U C
      (ExteriorAlgebra.ι (R (N + 1)) (jetVector N p (a.succAbove j).val)))).prod =
      (List.ofFn (fun j : Fin q => (shiftedEuler c)^[(a.succAbove j).val]
        (evalEuler p c (ExteriorAlgebra.iotaSeries (R := S) C)))).prod := by
    congr 1
    apply List.ofFn_inj.mpr
    funext j
    apply seriesJetMap_jetVector
    have := (a.succAbove j).isLt
    omega
  change ((-1 : PowerSeries (ExteriorAlgebra S M)) ^ a.val * _) * _ = _
  simp only [Function.comp_def]
  rw [hprod]
  simp only [Algebra.smul_def, map_pow, map_neg, map_one, mul_assoc]

/-- The finite ordinary-jet derivative specializes to its explicit binomial
Leibniz sum, preserving the order of the even and odd factors. -/
theorem seriesJetMap_bDerivative_fin (N n k : ℕ) (b c : ℤ)
    (U : PowerSeries S) (C : ℕ → M) :
    seriesJetMap n b c U C (bDerivative N n k) =
      ∑ a : Fin n, ∑ j : Fin n, if a.val + j.val = k + 1 then
        bDerivativeCoefficient N k a.val j.val •
          ((shiftedEuler b)^[a.val]
              (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) U) *
            (shiftedEuler c)^[j.val] (ExteriorAlgebra.iotaSeries (R := S) C)) else 0 := by
  simp only [bDerivative, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with haj
  · rw [seriesJetMap_smul, map_mul, map_intCast, evenJetMap_evenJet,
      map_mul, map_intCast, map_iterate_shiftedEuler_scalar, seriesJetMap_oddJet,
      mul_assoc]
    exact Int.cast_smul_eq_zsmul (PowerSeries (ExteriorAlgebra S M)) _ _
  · exact map_zero _

/-- On each odd generator, the universal Koszul differential specializes
to the divided Euler derivative of the actual scalar power. -/
theorem seriesJetMap_d_xi (N n : ℕ) (b c : ℤ) (U : PowerSeries S)
    (C : ℕ → M) (j : Fin n) :
    seriesJetMap n b c U C (d N n (xi n j)) =
      PowerSeries.map (algebraMap S (ExteriorAlgebra S M))
        (hasseEuler ((N : ℤ) * b) j.val (U ^ N)) := by
  rw [d_xi, seriesJetMap_algebraMap, evenJetMap_differentialCoefficient]

/-- The selector deletion formula is the specialization of an actual
universal boundary, before any homology argument. -/
theorem seriesJetMap_d_selectorProduct (N q : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree + q ≤ N) (b c : ℤ) (U : PowerSeries S) (C : ℕ → M) :
    seriesJetMap (N + 1) b c U C (d N (N + 1) (selectorProduct N q p)) =
      CoefficientSelector.eulerDeletionSeries q p c ((N : ℤ) * b)
        (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) (U ^ N))
        (ExteriorAlgebra.iotaSeries (R := S) C) := by
  rw [d_selectorProduct, seriesJetMap_selectorCycle N q p hp]

/-- The endpoint-aware finite binomial expression is the actual ordinary
Euler derivative of `f Dg - N (Df) g`. -/
theorem bDerivative_sum_eq_iterate {E : Type*} [Ring E]
    (N n k : ℕ) (hk : k + 1 < n) (b c : ℤ) (f g : PowerSeries E) :
    (∑ a : Fin n, ∑ j : Fin n, if a.val + j.val = k + 1 then
      bDerivativeCoefficient N k a.val j.val •
        ((shiftedEuler b)^[a.val] f * (shiftedEuler c)^[j.val] g) else 0) =
    (shiftedEuler (b + c))^[k]
      (f * shiftedEuler c g - N • (shiftedEuler b f * g)) := by
  let F : ℕ → ℕ → PowerSeries E := fun a j =>
    (shiftedEuler b)^[a] f * (shiftedEuler c)^[j] g
  have hsplit : (∑ a : Fin n, ∑ j : Fin n, if a.val + j.val = k + 1 then
      bDerivativeCoefficient N k a.val j.val • F a.val j.val else 0) =
      (∑ a : Fin n, ∑ j : Fin n, if a.val + j.val = k + 1 then
        rightLeibnizCoefficient k a.val j.val • F a.val j.val else 0) -
      N • (∑ a : Fin n, ∑ j : Fin n, if a.val + j.val = k + 1 then
        leftLeibnizCoefficient k a.val j.val • F a.val j.val else 0) := by
    simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp [bDerivativeCoefficient, sub_smul, mul_smul]
  change (∑ a : Fin n, ∑ j : Fin n, if a.val + j.val = k + 1 then
    bDerivativeCoefficient N k a.val j.val • F a.val j.val else 0) = _
  rw [hsplit]
  simp only [rightLeibnizCoefficient, leftLeibnizCoefficient]
  rw [sum_fin_right_jet_shift n k hk F, sum_fin_left_jet_shift n k hk F]
  have hlin : (shiftedEuler (b + c))^[k]
      (f * shiftedEuler c g - N • (shiftedEuler b f * g)) =
      (shiftedEuler (b + c))^[k] (f * shiftedEuler c g) -
      N • (shiftedEuler (b + c))^[k] (shiftedEuler b f * g) := by
    ext t : 1
    simp only [coeff_iterate_shiftedEuler, map_sub, map_nsmul, smul_sub]
    congr 1
    exact smul_comm _ _ _
  rw [hlin, iterate_shiftedEuler_mul, iterate_shiftedEuler_mul]
  simp only [F, Function.iterate_succ_apply]

/-- Ordinary universal differentiated cycles specialize to actual Euler
derivatives, with no derivation on the truncated source algebra. -/
theorem seriesJetMap_bDerivative (N n k : ℕ) (hk : k + 1 < n) (b c : ℤ)
    (U : PowerSeries S) (C : ℕ → M) :
    seriesJetMap n b c U C (bDerivative N n k) =
      (shiftedEuler (b + c))^[k]
        (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) U *
            shiftedEuler c (ExteriorAlgebra.iotaSeries (R := S) C) -
          N • (shiftedEuler b (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) U) *
            ExteriorAlgebra.iotaSeries (R := S) C)) := by
  rw [seriesJetMap_bDerivative_fin, bDerivative_sum_eq_iterate N n k hk]

/-- The finite differentiated-jet product maps to the ordered product of
Euler derivatives of the actual base cycle. -/
theorem seriesJetMap_orderedJetProduct (N a : ℕ) (s : Finset (Fin (a + 1)))
    (hzero : (0 : Fin (a + 1)) ∉ s) (b c : ℤ) (U : PowerSeries S) (C : ℕ → M) :
    seriesJetMap (a + 1) b c U C (orderedJetProduct N (a + 1) s) =
      orderedEulerProduct (a + 1) (b + c)
        (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) U *
            shiftedEuler c (ExteriorAlgebra.iotaSeries (R := S) C) -
          N • (shiftedEuler b (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) U) *
            ExteriorAlgebra.iotaSeries (R := S) C)) s := by
  simp only [orderedJetProduct, orderedEulerProduct, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjmem : j ∈ s := by simpa using hj
  have hjpos : 0 < j.val := by
    have hne : j ≠ 0 := fun h => hzero (h ▸ hjmem)
    have : j.val ≠ 0 := fun h => hne (Fin.ext h)
    omega
  exact seriesJetMap_bDerivative N (a + 1) (j.val - 1) (by have := j.isLt; omega)
    b c U C

/-- Specialize the finite universal polynomial identity using precisely the
same coefficient family. The zero-index support condition is the only
support information needed for substitution. -/
theorem specialize_universal_identity (N q : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree + q ≤ N)
    (coeff : Finset (Fin (N + 1)) → R (N + 1))
    (hzero : ∀ s, (0 : Fin (N + 1)) ∈ s → coeff s = 0)
    (hidentity : selectorCycle N q p =
      ∑ s : Finset (Fin (N + 1)), coeff s • orderedJetProduct N (N + 1) s)
    (b c : ℤ) (U : PowerSeries S) (C : ℕ → M) :
    CoefficientSelector.eulerDeletionSeries q p c ((N : ℤ) * b)
        (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) (U ^ N))
        (ExteriorAlgebra.iotaSeries (R := S) C) =
      jetExpression N coeff b (b + c) U
        (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) U *
            shiftedEuler c (ExteriorAlgebra.iotaSeries (R := S) C) -
          N • (shiftedEuler b (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) U) *
            ExteriorAlgebra.iotaSeries (R := S) C)) := by
  rw [← seriesJetMap_selectorCycle N q p hp b c U C, hidentity, map_sum]
  unfold jetExpression
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : (0 : Fin (N + 1)) ∈ s
  · simp [hzero s hs]
  · rw [seriesJetMap_smul, seriesJetMap_orderedJetProduct N N s hs]

/-- The finite universal identity admits a genuine series specialization.
Its coefficients remain polynomials of degree `N-q`; no variable or formal
series is inverted in obtaining the equality. -/
theorem exists_specialized_universal_identity (N q : ℕ) (p : Polynomial ℚ)
    (hp : p.natDegree + q ≤ N) :
    ∃ coeff : Finset (Fin (N + 1)) → R (N + 1),
      (∀ s, (coeff s).IsHomogeneous (N - q)) ∧
      (∀ s, (0 : Fin (N + 1)) ∈ s ∨ s.card ≠ q → coeff s = 0) ∧
      ∀ (b c : ℤ) (U : PowerSeries S) (C : ℕ → M),
        CoefficientSelector.eulerDeletionSeries q p c ((N : ℤ) * b)
            (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) (U ^ N))
            (ExteriorAlgebra.iotaSeries (R := S) C) =
          jetExpression N coeff b (b + c) U
            (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) U *
                shiftedEuler c (ExteriorAlgebra.iotaSeries (R := S) C) -
              N • (shiftedEuler b (PowerSeries.map (algebraMap S (ExteriorAlgebra S M)) U) *
                ExteriorAlgebra.iotaSeries (R := S) C)) := by
  obtain ⟨coeff, hc, _⟩ := universal_exterior_identity N q p (by omega)
  refine ⟨coeff, hc.1, hc.2.1, ?_⟩
  intro b c U C
  exact specialize_universal_identity N q p hp coeff
    (fun s hs => hc.2.1 s (Or.inl hs)) hc.2.2 b c U C

end TorusLinkHomology.UniversalJets
