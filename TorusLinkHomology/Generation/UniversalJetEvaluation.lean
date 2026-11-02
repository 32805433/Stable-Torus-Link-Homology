import TorusLinkHomology.Basic
import TorusLinkHomology.Generation.JetSeries

/-! # Evaluating universal jet expressions in coefficient series

The even variables are divided Euler jets. Odd differentiated generators
are evaluated in their specified order, so no commutativity of the chain
algebra is assumed.
-/

noncomputable section

open scoped BigOperators

namespace PowerSeries

variable {K E : Type*} [CommRing K] [Ring E] [Algebra K E]

/-- Series whose coefficients all lie in a specified subalgebra. -/
def coeffSubalgebra (S : Subalgebra K E) : Subalgebra K (PowerSeries E) where
  carrier := {f | ∀ j, f.coeff j ∈ S}
  add_mem' := by
    intro f g hf hg j
    simpa only [map_add] using S.add_mem (hf j) (hg j)
  mul_mem' := by
    intro f g hf hg j
    rw [coeff_mul]
    exact S.sum_mem fun ij _ => S.mul_mem (hf ij.1) (hg ij.2)
  algebraMap_mem' := by
    intro a j
    rw [Algebra.algebraMap_eq_smul_one, coeff_smul, coeff_one]
    split_ifs
    · simpa only [← Algebra.algebraMap_eq_smul_one] using S.algebraMap_mem a
    · simpa only [smul_zero] using S.zero_mem

@[simp] theorem mem_coeffSubalgebra (S : Subalgebra K E) (f : PowerSeries E) :
    f ∈ coeffSubalgebra S ↔ ∀ j, f.coeff j ∈ S := Iff.rfl

theorem shiftedEuler_mem_coeffSubalgebra (S : Subalgebra K E) (b : ℤ)
    {f : PowerSeries E} (hf : f ∈ coeffSubalgebra S) :
    TorusLinkHomology.CoefficientSeries.shiftedEuler b f ∈ coeffSubalgebra S := by
  intro j
  rw [TorusLinkHomology.CoefficientSeries.coeff_shiftedEuler]
  exact S.zsmul_mem (hf j) _

theorem iterate_shiftedEuler_mem_coeffSubalgebra (S : Subalgebra K E) (b : ℤ)
    (k : ℕ) {f : PowerSeries E} (hf : f ∈ coeffSubalgebra S) :
    (TorusLinkHomology.CoefficientSeries.shiftedEuler b)^[k] f ∈ coeffSubalgebra S := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact shiftedEuler_mem_coeffSubalgebra S b ih

end PowerSeries

namespace TorusLinkHomology.UniversalJets

variable {R E : Type*} [CommRing R] [Algebra ℚ R] [Ring E] [Algebra R E]

/-- Substitute divided Euler jets for the finite even variables. -/
def evenJetMap (n : ℕ) (b : ℤ) (U : PowerSeries R) :
    TorusLinkHomology.R n →+* PowerSeries R :=
  MvPolynomial.eval₂Hom (algebraMap ℚ (PowerSeries R))
    (fun j => CoefficientSeries.hasseEuler b j.val U)

@[simp] theorem evenJetMap_X (n : ℕ) (b : ℤ) (U : PowerSeries R) (j : Fin n) :
    evenJetMap n b U (MvPolynomial.X j) = CoefficientSeries.hasseEuler b j.val U := by
  simp [evenJetMap]

@[simp] theorem evenJetMap_C (n : ℕ) (b : ℤ) (U : PowerSeries R) (a : ℚ) :
    evenJetMap n b U (MvPolynomial.C a) = algebraMap ℚ (PowerSeries R) a := by
  simp [evenJetMap]

/-- Evaluate an ordered product of ordinary differentiated odd generators. -/
def orderedEulerProduct (n : ℕ) (b : ℤ) (P : PowerSeries E) (s : Finset (Fin n)) :
    PowerSeries E :=
  (s.sort.map (fun j => (CoefficientSeries.shiftedEuler b)^[j.val - 1] P)).prod

/-- The polynomial expression supplied by the finite universal identity,
evaluated at the chosen even and odd series. -/
def jetExpression (N : ℕ)
    (c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1))
    (r b : ℤ) (U : PowerSeries R) (P : PowerSeries E) : PowerSeries E :=
  ∑ s : Finset (Fin (N + 1)),
    PowerSeries.map (algebraMap R E) (evenJetMap (N + 1) r U (c s)) *
      orderedEulerProduct (N + 1) b P s

theorem orderedEulerProduct_mem_coeffSubalgebra {K : Type*} [CommRing K] [Algebra K E]
    (S : Subalgebra K E) (n : ℕ) (b : ℤ) (P : PowerSeries E) (s : Finset (Fin n))
    (hP : P ∈ PowerSeries.coeffSubalgebra S) :
    orderedEulerProduct n b P s ∈ PowerSeries.coeffSubalgebra S := by
  unfold orderedEulerProduct
  apply Subalgebra.list_prod_mem
  intro f hf
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
  exact PowerSeries.iterate_shiftedEuler_mem_coeffSubalgebra S b _ hP

theorem jetExpression_mem_coeffSubalgebra {K : Type*} [CommRing K] [Algebra K E]
    (S : Subalgebra K E) (N : ℕ)
    (c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1))
    (r b : ℤ) (U : PowerSeries R) (P : PowerSeries E)
    (hc : ∀ s, PowerSeries.map (algebraMap R E) (evenJetMap (N + 1) r U (c s)) ∈
      PowerSeries.coeffSubalgebra S) (hP : P ∈ PowerSeries.coeffSubalgebra S) :
    jetExpression N c r b U P ∈ PowerSeries.coeffSubalgebra S := by
  apply Subalgebra.sum_mem
  intro s _
  exact Subalgebra.mul_mem _ (hc s)
    (orderedEulerProduct_mem_coeffSubalgebra S (N + 1) b P s hP)

/-- The even coefficient ring is contained in every algebra of cycles or
tail-generated representatives over that ring. -/
theorem jetExpression_coeff_mem (S : Subalgebra R E) (N : ℕ)
    (c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1))
    (r b : ℤ) (U : PowerSeries R) (P : PowerSeries E)
    (hP : ∀ j, P.coeff j ∈ S) (j : ℕ) : (jetExpression N c r b U P).coeff j ∈ S := by
  apply jetExpression_mem_coeffSubalgebra S N c r b U P _ hP j
  intro s i
  rw [PowerSeries.coeff_map]
  exact S.algebraMap_mem _

theorem map_orderedEulerProduct {F : Type*} [Ring F] (f : E →+* F)
    (n : ℕ) (b : ℤ) (P : PowerSeries E) (s : Finset (Fin n)) :
    PowerSeries.map f (orderedEulerProduct n b P s) =
      orderedEulerProduct n b (PowerSeries.map f P) s := by
  simp only [orderedEulerProduct, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  ext t : 1
  simp only [PowerSeries.coeff_map, CoefficientSeries.coeff_iterate_shiftedEuler,
    map_zsmul, Function.comp_apply]

theorem map_evenJetMap {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →+* S) (n : ℕ) (b : ℤ) (U : PowerSeries R) (a : TorusLinkHomology.R n) :
    PowerSeries.map f (evenJetMap n b U a) =
      evenJetMap n b (PowerSeries.map f U) a := by
  induction a using MvPolynomial.induction_on with
  | C a =>
    simp only [evenJetMap_C, PowerSeries.algebraMap_apply, PowerSeries.map_C]
    exact congrArg PowerSeries.C (f.map_rat_algebraMap a)
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a j ha =>
    simp only [map_mul, ha, evenJetMap_X]
    congr 1
    ext t : 1
    simp only [PowerSeries.coeff_map, CoefficientSeries.coeff_hasseEuler, map_rat_smul]

/-- Evaluation commutes with coefficient specialization, even when the
exterior coefficient algebras are noncommutative. -/
theorem map_jetExpression {S F : Type*} [CommRing S] [Algebra ℚ S]
    [Ring F] [Algebra S F] (f : R →+* S) (g : E →+* F)
    (hfg : ∀ a, g (algebraMap R E a) = algebraMap S F (f a))
    (N : ℕ) (c : Finset (Fin (N + 1)) → TorusLinkHomology.R (N + 1))
    (r b : ℤ) (U : PowerSeries R) (P : PowerSeries E) :
    PowerSeries.map g (jetExpression N c r b U P) =
      jetExpression N c r b (PowerSeries.map f U) (PowerSeries.map g P) := by
  simp only [jetExpression, map_sum, map_mul, map_orderedEulerProduct]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rw [← map_evenJetMap f (N + 1) r U (c s)]
  ext t : 1
  simp only [PowerSeries.coeff_map, hfg]

end TorusLinkHomology.UniversalJets
