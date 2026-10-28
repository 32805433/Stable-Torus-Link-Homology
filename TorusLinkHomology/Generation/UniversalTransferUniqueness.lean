import TorusLinkHomology.Generation.CoordinateKoszul
import TorusLinkHomology.Generation.ComparisonExactness
import TorusLinkHomology.Generation.UniversalConnecting

/-!
# The finite exterior decomposition for universal-transfer uniqueness

All coefficient comparisons take place in the free polynomial ring. The
Q-degree is the number of Q-generators in an exterior basis monomial.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.UniversalTransfer

local instance oddIndexOrder : LinearOrder (ℕ ⊕ ℕ) :=
  inferInstanceAs (LinearOrder (ℕ ⊕ₗ ℕ))

def oddBasis : Module.Basis (ℕ ⊕ ℕ) R V := Finsupp.basisSingleOne

def chainBasis : Module.Basis (Finset (ℕ ⊕ ℕ)) R A := oddBasis.ExteriorAlgebra

def qCount (s : Finset (ℕ ⊕ ℕ)) : ℕ := (s.filter (fun i => i.isRight = true)).card

@[simp] theorem qCount_empty : qCount ∅ = 0 := by simp [qCount]

@[simp] theorem qCount_singleton_A (i : ℕ) : qCount {Sum.inl i} = 0 := by
  unfold qCount
  rw [Finset.filter_singleton]
  simp [Sum.isRight]

@[simp] theorem qCount_singleton_Q (h : ℕ) : qCount {Sum.inr h} = 1 := by
  unfold qCount
  rw [Finset.filter_singleton]
  simp [Sum.isRight]

theorem qCount_union {s t : Finset (ℕ ⊕ ℕ)} (hst : Disjoint s t) :
    qCount (s ∪ t) = qCount s + qCount t := by
  unfold qCount
  rw [Finset.filter_union]
  apply Finset.card_union_of_disjoint
  exact hst.mono (Finset.filter_subset _ s) (Finset.filter_subset _ t)

/-- The component of fixed Q-degree, defined by finite exterior coordinates. -/
def qPart (q : ℕ) : A →ₗ[R] A where
  toFun x := chainBasis.repr.symm ((chainBasis.repr x).filter (fun s => qCount s = q))
  map_add' x y := by simp [map_add, Finsupp.filter_add]
  map_smul' c x := by simp [map_smul, Finsupp.filter_smul]

@[simp] theorem repr_qPart (q : ℕ) (x : A) (s : Finset (ℕ ⊕ ℕ)) :
    chainBasis.repr (qPart q x) s = if qCount s = q then chainBasis.repr x s else 0 := by
  simp [qPart, Finsupp.filter_apply]

@[simp] theorem qPart_basis (q : ℕ) (s : Finset (ℕ ⊕ ℕ)) :
    qPart q (chainBasis s) = if qCount s = q then chainBasis s else 0 := by
  apply chainBasis.repr.injective
  apply Finsupp.ext
  intro t
  by_cases hs : qCount s = q
  · simp only [hs, if_true, repr_qPart, Module.Basis.repr_self]
    by_cases hts : s = t
    · subst t; simp [hs]
    · simp [hts]
  · simp only [hs, if_false, repr_qPart, Module.Basis.repr_self, map_zero, Finsupp.zero_apply]
    by_cases hts : s = t
    · subst t; simp [hs]
    · simp [hts]

@[simp] theorem chainBasis_empty : chainBasis ∅ = 1 := by
  rw [chainBasis, ExteriorAlgebra.basis_apply_ofCard _ (show (∅ : Finset (ℕ ⊕ ℕ)).card = 0 from rfl)]
  exact ExteriorAlgebra.ιMulti_zero_apply _

@[simp] theorem chainBasis_singleton_A (i : ℕ) : chainBasis {Sum.inl i} = oddA i := by
  rw [chainBasis, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton _)]
  simp [ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_singleton, oddA, oddBasis]

@[simp] theorem chainBasis_singleton_Q (h : ℕ) : chainBasis {Sum.inr h} = oddQ h := by
  rw [chainBasis, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton _)]
  simp [ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_singleton, oddQ, oddBasis]

theorem qPart_basis_mul (q : ℕ) (s t : Finset (ℕ ⊕ ℕ)) :
    qPart q (chainBasis s * chainBasis t) =
      if qCount s + qCount t = q then chainBasis s * chainBasis t else 0 := by
  let S : Set.powersetCard (ℕ ⊕ ℕ) s.card := Set.powersetCard.ofCard rfl
  let T : Set.powersetCard (ℕ ⊕ ℕ) t.card := Set.powersetCard.ofCard rfl
  by_cases h : Disjoint s t
  · have hp := ExteriorAlgebra.basis_mul_of_disjoint oddBasis S T h
    change chainBasis s * chainBasis t = _ at hp
    rw [hp]
    simp only [Units.smul_def, map_zsmul]
    have hq : qCount (Set.powersetCard.disjUnion (s := S) (t := T) h).val =
        qCount s + qCount t := by
      change qCount (s.disjUnion t h) = _
      rw [Finset.disjUnion_eq_union, qCount_union h]
    have hpart : qPart q (oddBasis.ExteriorAlgebra (Set.powersetCard.disjUnion (s := S) (t := T) h)) =
        if qCount s + qCount t = q then
          oddBasis.ExteriorAlgebra (Set.powersetCard.disjUnion (s := S) (t := T) h) else 0 := by
      change qPart q (chainBasis _) = if qCount s + qCount t = q then chainBasis _ else 0
      rw [qPart_basis, hq]
    rw [hpart]
    split_ifs <;> simp
  · have hp := ExteriorAlgebra.basis_mul_of_not_disjoint oddBasis S T h
    change chainBasis s * chainBasis t = 0 at hp
    rw [hp, map_zero]
    split_ifs <;> rfl

theorem qPart_oddA_mul (q i : ℕ) (x : A) :
    qPart q (oddA i * x) = oddA i * qPart q x := by
  have heq : (qPart q).comp (LinearMap.mulLeft R (oddA i)) =
      (LinearMap.mulLeft R (oddA i)).comp (qPart q) := by
    apply chainBasis.ext
    intro s
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [← chainBasis_singleton_A, qPart_basis_mul, qCount_singleton_A, zero_add, qPart_basis]
    split_ifs <;> simp
  exact LinearMap.congr_fun heq x

theorem qPart_zero_oddQ_mul (h : ℕ) (x : A) : qPart 0 (oddQ h * x) = 0 := by
  have heq : (qPart 0).comp (LinearMap.mulLeft R (oddQ h)) = 0 := by
    apply chainBasis.ext
    intro s
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply]
    rw [← chainBasis_singleton_Q, qPart_basis_mul, qCount_singleton_Q, if_neg (by omega)]
  exact LinearMap.congr_fun heq x

theorem qPart_succ_oddQ_mul (q h : ℕ) (x : A) :
    qPart (q + 1) (oddQ h * x) = oddQ h * qPart q x := by
  have heq : (qPart (q + 1)).comp (LinearMap.mulLeft R (oddQ h)) =
      (LinearMap.mulLeft R (oddQ h)).comp (qPart q) := by
    apply chainBasis.ext
    intro s
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    rw [← chainBasis_singleton_Q, qPart_basis_mul, qCount_singleton_Q, qPart_basis]
    have hiff : 1 + qCount s = q + 1 ↔ qCount s = q := by omega
    simp only [hiff]
    split_ifs <;> simp
  exact LinearMap.congr_fun heq x

/-- Induction over the named odd generators, valid for their infinite index
set because every Finsupp and every exterior expression has finite support. -/
theorem induction_on_generators {P : A → Prop}
    (hone : P 1) (hadd : ∀ a b, P a → P b → P (a + b))
    (hsmul : ∀ (c : R) a, P a → P (c • a))
    (hodd : ∀ i : ℕ ⊕ ℕ, ∀ a, P a → P (ExteriorAlgebra.ι R (Finsupp.single i 1) * a))
    (x : A) : P x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simpa [Algebra.algebraMap_eq_smul_one] using hsmul c 1 hone
  | add a b ha hb => exact hadd a b ha hb
  | ι_mul a v ha =>
    have hv : (∑ i ∈ v.support, v i • Finsupp.single i (1 : R)) = v := by
      simpa [oddBasis, Finsupp.linearCombination_apply, Finsupp.sum] using oddBasis.linearCombination_repr v
    change P (ExteriorAlgebra.ι R v * a)
    rw [← hv, map_sum, Finset.sum_mul]
    simp only [map_smul, smul_mul_assoc]
    apply Finset.sum_induction _ _ hadd
    · simpa using hsmul 0 1 hone
    · intro i _
      exact hsmul (v i) _ (hodd i a ha)

/-- Coefficient differentiation holds the exterior basis fixed. -/
def vDerivative (h : ℕ) : A →+ A :=
  chainBasis.coefficientConnection (MvPolynomial.pderiv (Sum.inr h))

@[simp] theorem repr_vDerivative (h : ℕ) (x : A) (s : Finset (ℕ ⊕ ℕ)) :
    chainBasis.repr (vDerivative h x) s =
      MvPolynomial.pderiv (Sum.inr h) (chainBasis.repr x s) :=
  Module.Basis.repr_coefficientConnection _ _ _ _

/-- A no-v expression has zero coefficient derivative in every v-variable. -/
def NoV (x : A) : Prop := ∀ h : ℕ, vDerivative h x = 0

@[simp] theorem vDerivative_basis (h : ℕ) (s : Finset (ℕ ⊕ ℕ)) :
    vDerivative h (chainBasis s) = 0 := Module.Basis.coefficientConnection_basis _ _ _

theorem vDerivative_smul (h : ℕ) (c : R) (x : A) :
    vDerivative h (c • x) = MvPolynomial.pderiv (Sum.inr h) c • x + c • vDerivative h x :=
  Module.Basis.coefficientConnection_smul _ _ _ _

theorem vDerivative_basis_mul (h : ℕ) (s t : Finset (ℕ ⊕ ℕ)) :
    vDerivative h (chainBasis s * chainBasis t) = 0 := by
  let S : Set.powersetCard (ℕ ⊕ ℕ) s.card := Set.powersetCard.ofCard rfl
  let T : Set.powersetCard (ℕ ⊕ ℕ) t.card := Set.powersetCard.ofCard rfl
  change vDerivative h (oddBasis.ExteriorAlgebra S * oddBasis.ExteriorAlgebra T) = 0
  by_cases hst : Disjoint s t
  · rw [ExteriorAlgebra.basis_mul_of_disjoint oddBasis S T hst]
    simp only [Units.smul_def, map_zsmul]
    change _ • vDerivative h (chainBasis _) = 0
    rw [vDerivative_basis, smul_zero]
  · rw [ExteriorAlgebra.basis_mul_of_not_disjoint oddBasis S T hst, map_zero]

theorem vDerivative_basis_mul_arbitrary (h : ℕ) (s : Finset (ℕ ⊕ ℕ)) (x : A) :
    vDerivative h (chainBasis s * x) = chainBasis s * vDerivative h x := by
  have hcomm := chainBasis.coefficientConnection_commute_of_basis
    (MvPolynomial.pderiv (Sum.inr h)) (LinearMap.mulLeft R (chainBasis s)) 0
    (fun t => vDerivative_basis_mul h s t) x
  simpa [vDerivative] using hcomm

theorem vDerivative_odd_mul (h : ℕ) (i : ℕ ⊕ ℕ) (x : A) :
    vDerivative h (ExteriorAlgebra.ι R (Finsupp.single i 1) * x) =
      ExteriorAlgebra.ι R (Finsupp.single i 1) * vDerivative h x := by
  cases i with
  | inl i =>
    change vDerivative h (oddA i * x) = oddA i * vDerivative h x
    rw [← chainBasis_singleton_A]
    exact vDerivative_basis_mul_arbitrary h {Sum.inl i} x
  | inr i =>
    change vDerivative h (oddQ i * x) = oddQ i * vDerivative h x
    rw [← chainBasis_singleton_Q]
    exact vDerivative_basis_mul_arbitrary h {Sum.inr i} x

def vFunctionalDerivative (h : ℕ) (f : Module.Dual R V) : Module.Dual R V :=
  Finsupp.linearCombination R (fun i => MvPolynomial.pderiv (Sum.inr h) (f (Finsupp.single i 1)))

theorem vDerivative_contractLeft (h : ℕ) (f : Module.Dual R V) (x : A) :
    vDerivative h (CliffordAlgebra.contractLeft (Q := 0) f x) =
      CliffordAlgebra.contractLeft (Q := 0) f (vDerivative h x) +
        CliffordAlgebra.contractLeft (Q := 0) (vFunctionalDerivative h f) x := by
  induction x using induction_on_generators with
  | hone =>
    rw [CliffordAlgebra.contractLeft_one, map_zero, ← chainBasis_empty,
      vDerivative_basis, map_zero]
    simp
  | hadd a b ha hb => simp only [map_add, ha, hb]; abel
  | hsmul c a ha =>
    simp only [map_smul, vDerivative_smul, map_add, ha, smul_add]
    abel
  | hodd i a ha =>
    simp only [CliffordAlgebra.contractLeft_ι_mul, map_sub, vDerivative_smul,
      vDerivative_odd_mul, ha, vFunctionalDerivative, Finsupp.linearCombination_single,
      one_smul, mul_add]
    abel

theorem NoV.qPart {x : A} (hx : NoV x) (q : ℕ) : NoV (qPart q x) := by
  intro h
  apply chainBasis.repr.injective
  apply Finsupp.ext
  intro s
  have hzero := congrArg (fun z => chainBasis.repr z s) (hx h)
  simp only [repr_vDerivative, map_zero, Finsupp.zero_apply] at hzero ⊢
  rw [repr_qPart]
  split_ifs <;> simp_all

def functionalA (N m : ℕ) : Module.Dual R V :=
  Finsupp.linearCombination R (Sum.elim (fun i => shiftedV m i - g N i) (fun _ => 0))

def functionalQ (N m : ℕ) : Module.Dual R V :=
  Finsupp.linearCombination R (Sum.elim (fun _ => 0) (qEquation N m))

def dA (N m : ℕ) : A →ₗ[R] A := CliffordAlgebra.contractLeft (Q := 0) (functionalA N m)

def dQ (N m : ℕ) : A →ₗ[R] A := CliffordAlgebra.contractLeft (Q := 0) (functionalQ N m)

theorem functional_eq_add (N m : ℕ) : functional N m = functionalA N m + functionalQ N m := by
  apply Finsupp.lhom_ext
  intro i c
  cases i <;> simp [functional, functionalA, functionalQ, equation]

theorem d_eq_add (N m : ℕ) (x : A) : d N m x = dA N m x + dQ N m x := by
  change CliffordAlgebra.contractLeft (Q := 0) (functional N m) x = _
  rw [functional_eq_add, map_add, LinearMap.add_apply]
  rfl

@[simp] theorem qPart_one (q : ℕ) : qPart q 1 = if q = 0 then 1 else 0 := by
  rw [← chainBasis_empty, qPart_basis, qCount_empty]
  by_cases hq : q = 0 <;> simp [hq, eq_comm]

@[simp] theorem dA_one (N m : ℕ) : dA N m 1 = 0 := CliffordAlgebra.contractLeft_one _ _

@[simp] theorem dQ_one (N m : ℕ) : dQ N m 1 = 0 := CliffordAlgebra.contractLeft_one _ _

theorem dA_oddA_mul (N m i : ℕ) (x : A) :
    dA N m (oddA i * x) = (shiftedV m i - g N i) • x - oddA i * dA N m x := by
  simp [dA, oddA, CliffordAlgebra.contractLeft_ι_mul, functionalA]

theorem dA_oddQ_mul (N m h : ℕ) (x : A) :
    dA N m (oddQ h * x) = -(oddQ h * dA N m x) := by
  simp [dA, oddQ, CliffordAlgebra.contractLeft_ι_mul, functionalA]

theorem dQ_oddA_mul (N m i : ℕ) (x : A) :
    dQ N m (oddA i * x) = -(oddA i * dQ N m x) := by
  simp [dQ, oddA, CliffordAlgebra.contractLeft_ι_mul, functionalQ]

theorem dQ_oddQ_mul (N m h : ℕ) (x : A) :
    dQ N m (oddQ h * x) = qEquation N m h • x - oddQ h * dQ N m x := by
  simp [dQ, oddQ, CliffordAlgebra.contractLeft_ι_mul, functionalQ]

theorem dQ_qPart_zero (N m : ℕ) (x : A) : dQ N m (qPart 0 x) = 0 := by
  induction x using induction_on_generators with
  | hone => simp
  | hadd a b ha hb => simp only [map_add, ha, hb, add_zero]
  | hsmul c a ha => simp only [map_smul, ha, smul_zero]
  | hodd i a ha =>
    cases i with
    | inl i =>
      change dQ N m (qPart 0 (oddA i * a)) = 0
      rw [qPart_oddA_mul, dQ_oddA_mul, ha, mul_zero, neg_zero]
    | inr h =>
      change dQ N m (qPart 0 (oddQ h * a)) = 0
      rw [qPart_zero_oddQ_mul, map_zero]

/-- The A-part of the differential preserves the number of Q-factors. -/
theorem qPart_dA (N m : ℕ) (x : A) (q : ℕ) :
    qPart q (dA N m x) = dA N m (qPart q x) := by
  induction x using induction_on_generators generalizing q with
  | hone => simp only [dA_one, map_zero, qPart_one]; split_ifs <;> simp
  | hadd a b ha hb => simp only [map_add, ha, hb]
  | hsmul c a ha => simp only [map_smul, ha]
  | hodd i a ha =>
    cases i with
    | inl i =>
      change qPart q (dA N m (oddA i * a)) = dA N m (qPart q (oddA i * a))
      rw [dA_oddA_mul, map_sub, map_smul, qPart_oddA_mul, qPart_oddA_mul,
        dA_oddA_mul, ha]
    | inr h =>
      change qPart q (dA N m (oddQ h * a)) = dA N m (qPart q (oddQ h * a))
      cases q with
      | zero => rw [dA_oddQ_mul, map_neg, qPart_zero_oddQ_mul, qPart_zero_oddQ_mul, map_zero, neg_zero]
      | succ q =>
        rw [dA_oddQ_mul, map_neg, qPart_succ_oddQ_mul, qPart_succ_oddQ_mul, dA_oddQ_mul, ha]

/-- The Q-part of the differential lowers Q-degree by one. -/
theorem qPart_dQ (N m : ℕ) (x : A) (q : ℕ) :
    qPart q (dQ N m x) = dQ N m (qPart (q + 1) x) := by
  induction x using induction_on_generators generalizing q with
  | hone => simp
  | hadd a b ha hb => simp only [map_add, ha, hb]
  | hsmul c a ha => simp only [map_smul, ha]
  | hodd i a ha =>
    cases i with
    | inl i =>
      change qPart q (dQ N m (oddA i * a)) = dQ N m (qPart (q + 1) (oddA i * a))
      rw [dQ_oddA_mul, map_neg, qPart_oddA_mul, qPart_oddA_mul, dQ_oddA_mul, ha]
    | inr h =>
      change qPart q (dQ N m (oddQ h * a)) = dQ N m (qPart (q + 1) (oddQ h * a))
      cases q with
      | zero =>
        rw [dQ_oddQ_mul, map_sub, map_smul, qPart_zero_oddQ_mul,
          qPart_succ_oddQ_mul, dQ_oddQ_mul, dQ_qPart_zero, mul_zero, sub_zero]
      | succ q =>
        rw [dQ_oddQ_mul, map_sub, map_smul, qPart_succ_oddQ_mul,
          qPart_succ_oddQ_mul, dQ_oddQ_mul, ha]

/-- Evaluation at Q=0, an algebra map rather than a chain map. -/
def eraseQVector : V →ₗ[R] V :=
  Finsupp.linearCombination R (Sum.elim
    (fun i => Finsupp.single (Sum.inl i) 1) (fun _ => 0))

def eraseQ : A →ₐ[R] A := ExteriorAlgebra.map eraseQVector

@[simp] theorem eraseQ_oddA (i : ℕ) : eraseQ (oddA i) = oddA i := by
  simp [eraseQ, eraseQVector, oddA]

@[simp] theorem eraseQ_oddQ (h : ℕ) : eraseQ (oddQ h) = 0 := by
  simp [eraseQ, eraseQVector, oddQ]

theorem eraseQ_eq_qPart_zero (x : A) : eraseQ x = qPart 0 x := by
  induction x using induction_on_generators with
  | hone => simp
  | hadd a b ha hb => simp only [map_add, ha, hb]
  | hsmul c a ha => simp only [map_smul, ha]
  | hodd i a ha =>
    cases i with
    | inl i =>
      change eraseQ (oddA i * a) = qPart 0 (oddA i * a)
      rw [map_mul, eraseQ_oddA, ha, qPart_oddA_mul]
    | inr h =>
      change eraseQ (oddQ h * a) = qPart 0 (oddQ h * a)
      rw [map_mul, eraseQ_oddQ, zero_mul, qPart_zero_oddQ_mul]

/-- Delete one distinguished exterior generator. -/
def eraseOne (i : ℕ ⊕ ℕ) : A →ₐ[R] A :=
  ExteriorAlgebra.map (ExteriorAlgebra.contractionProjection (Finsupp.lapply i) (Finsupp.single i 1))

theorem eraseOne_basis (i : ℕ ⊕ ℕ) (s : Finset (ℕ ⊕ ℕ)) :
    eraseOne i (chainBasis s) = if i ∈ s then 0 else chainBasis s := by
  rw [eraseOne, chainBasis, ExteriorAlgebra.basis_apply]
  unfold ExteriorAlgebra.ιMulti_family
  rw [ExteriorAlgebra.map_apply_ιMulti]
  let e : Fin s.card → (ℕ ⊕ ℕ) := s.orderEmbOfFin rfl
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    have hm : i ∈ Set.range e :=
      by simpa [e, Finset.range_orderEmbOfFin] using hi
    obtain ⟨j, hj⟩ := hm
    apply (ExteriorAlgebra.ιMulti R s.card).map_coord_zero j
    change ExteriorAlgebra.contractionProjection (Finsupp.lapply i) (Finsupp.single i 1)
      (oddBasis (e j)) = 0
    rw [hj]
    simp [oddBasis]
  · rw [if_neg hi]
    congr 1
    funext j
    have hj : e j ∈ s := s.orderEmbOfFin_mem rfl j
    have hne : e j ≠ i := by intro heq; exact hi (heq ▸ hj)
    change ExteriorAlgebra.contractionProjection (Finsupp.lapply i) (Finsupp.single i 1)
      (oddBasis (e j)) = oddBasis (e j)
    simp only [oddBasis, ExteriorAlgebra.contractionProjection_apply, Finsupp.lapply_apply,
      Finsupp.coe_basisSingleOne]
    rw [Finsupp.single_eq_of_ne hne.symm, zero_smul, sub_zero]

theorem repr_eraseOne_of_mem (i : ℕ ⊕ ℕ) (x : A) (s : Finset (ℕ ⊕ ℕ)) (hi : i ∈ s) :
    chainBasis.repr (eraseOne i x) s = 0 := by
  have hmap : (chainBasis.coord s).comp (eraseOne i).toLinearMap = 0 := by
    apply chainBasis.ext
    intro t
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Module.Basis.coord_apply,
      LinearMap.zero_apply, eraseOne_basis]
    by_cases ht : i ∈ t
    · simp [ht]
    · have hne : t ≠ s := by intro heq; exact ht (heq ▸ hi)
      simp [ht, Module.Basis.repr_self, hne]
  exact LinearMap.congr_fun hmap x

theorem coefficient_eq_zero_of_coordinate_contraction_eq_zero (i : ℕ ⊕ ℕ)
    (x : A) (hx : CliffordAlgebra.contractLeft (Q := 0) (Finsupp.lapply i) x = 0)
    (s : Finset (ℕ ⊕ ℕ)) (hi : i ∈ s) : chainBasis.repr x s = 0 := by
  have heq : eraseOne i x = x := by
    rw [eraseOne, ExteriorAlgebra.map_contractionProjection, hx, mul_zero, sub_zero]
  rw [← heq]
  exact repr_eraseOne_of_mem i x s hi

theorem contractLeft_iotaMulti_congr (f g : Module.Dual R V) (q : ℕ) (w : Fin q → V)
    (h : ∀ j, f (w j) = g (w j)) :
    CliffordAlgebra.contractLeft (Q := 0) f (ExteriorAlgebra.ιMulti R q w) =
      CliffordAlgebra.contractLeft (Q := 0) g (ExteriorAlgebra.ιMulti R q w) := by
  induction q with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul,
      CliffordAlgebra.contractLeft_ι_mul, h 0]
    rw [ih (Matrix.vecTail w) (fun j => h j.succ)]

/-- A contraction on a finite expression only uses functional values on
the odd generators occurring in its nonzero exterior coordinates. -/
theorem contractLeft_eq_of_support (f g : Module.Dual R V) (x : A)
    (h : ∀ s, chainBasis.repr x s ≠ 0 → ∀ i ∈ s,
      f (Finsupp.single i 1) = g (Finsupp.single i 1)) :
    CliffordAlgebra.contractLeft (Q := 0) f x = CliffordAlgebra.contractLeft (Q := 0) g x := by
  have hexp : (∑ s ∈ (chainBasis.repr x).support, chainBasis.repr x s • chainBasis s) = x := by
    simpa [Finsupp.linearCombination_apply, Finsupp.sum] using chainBasis.linearCombination_repr x
  rw [← hexp, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_smul, map_smul]
  congr 1
  rw [chainBasis, ExteriorAlgebra.basis_apply]
  unfold ExteriorAlgebra.ιMulti_family
  apply contractLeft_iotaMulti_congr
  intro j
  apply h s (Finsupp.mem_support_iff.mp hs)
  exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ _).mp ⟨j, rfl⟩

/-- The finite set of Q-indices actually appearing in a chain. -/
def qSupport (x : A) : Finset ℕ :=
  (chainBasis.repr x).support.biUnion Finset.toRight

theorem mem_qSupport_iff (x : A) (h : ℕ) :
    h ∈ qSupport x ↔ ∃ s, chainBasis.repr x s ≠ 0 ∧ Sum.inr h ∈ s := by
  simp [qSupport, Finset.mem_biUnion, Finsupp.mem_support_iff]

/-- At the largest occurring Q-index, coefficient differentiation of dQ
is a nonzero scalar times its distinguished exterior contraction. -/
theorem top_vDerivative_dQ (N m H : ℕ) (x : A)
    (hbound : ∀ h ∈ qSupport x, h ≤ H) :
    CliffordAlgebra.contractLeft (Q := 0) (vFunctionalDerivative H (functionalQ N m)) x =
      MvPolynomial.pderiv (Sum.inr H) (qEquation N m H) •
        CliffordAlgebra.contractLeft (Q := 0) (Finsupp.lapply (Sum.inr H)) x := by
  let c := MvPolynomial.pderiv (Sum.inr H) (qEquation N m H)
  have heq := contractLeft_eq_of_support (vFunctionalDerivative H (functionalQ N m))
    (c • Finsupp.lapply (Sum.inr H)) x
  have hagree : ∀ s : Finset (ℕ ⊕ ℕ), chainBasis.repr x s ≠ 0 → ∀ i : ℕ ⊕ ℕ, i ∈ s →
      vFunctionalDerivative H (functionalQ N m) (Finsupp.single i 1) =
        (c • (Finsupp.lapply (Sum.inr H) : Module.Dual R V)) (Finsupp.single i 1) := by
    intro s hs i hi
    cases i with
    | inl i => simp [vFunctionalDerivative, functionalQ]
    | inr j =>
      have hj : j ≤ H := hbound j ((mem_qSupport_iff x j).mpr ⟨s, hs, hi⟩)
      by_cases heq : j = H
      · subst j
        simp [vFunctionalDerivative, functionalQ, c]
      · have hjlt : j < H := by omega
        simp only [vFunctionalDerivative, Finsupp.linearCombination_single,
          functionalQ, Sum.elim_inr, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul, one_mul]
        rw [pderiv_qEquation_of_lt N m j H hjlt]
        have hne : (Sum.inr j : ℕ ⊕ ℕ) ≠ Sum.inr H := by simpa using heq
        rw [Finsupp.single_eq_of_ne hne.symm, mul_zero]
  rw [heq hagree, map_smul, LinearMap.smul_apply]

/-- A no-v cycle for dQ cannot contain any Q-generator. The cancellation is
in the free exterior module, using the nonzero universal polynomial scalar. -/
theorem qSupport_eq_empty_of_dQ (N m : ℕ) (hN : 0 < N) (hm : 0 < m)
    (x : A) (hx : NoV x) (hcycle : dQ N m x = 0) : qSupport x = ∅ := by
  by_contra hne
  have hnonempty : (qSupport x).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  let H := (qSupport x).max' hnonempty
  have hH : H ∈ qSupport x := Finset.max'_mem _ _
  have hbound : ∀ h ∈ qSupport x, h ≤ H := fun h hh => Finset.le_max' _ _ hh
  have hd := vDerivative_contractLeft H (functionalQ N m) x
  change vDerivative H (dQ N m x) = dQ N m (vDerivative H x) + _ at hd
  rw [hcycle, map_zero, hx H, map_zero, zero_add, top_vDerivative_dQ N m H x hbound] at hd
  have hc := pderiv_qEquation_top_ne_zero N m H hN hm
  have hcontraction : CliffordAlgebra.contractLeft (Q := 0) (Finsupp.lapply (Sum.inr H)) x = 0 := by
    apply smul_injective _ hc
    change _ • CliffordAlgebra.contractLeft (Q := 0) (Finsupp.lapply (Sum.inr H)) x = _ • (0 : A)
    rw [smul_zero]
    exact hd.symm
  obtain ⟨s, hs, hHs⟩ := (mem_qSupport_iff x H).mp hH
  exact hs (coefficient_eq_zero_of_coordinate_contraction_eq_zero (Sum.inr H) x hcontraction s hHs)

/-- A positive Q-degree component with no occurring Q-index is zero. -/
theorem qPart_eq_zero_of_qSupport_eq_empty (q : ℕ) (hq : 0 < q) (x : A)
    (hsupport : qSupport (qPart q x) = ∅) : qPart q x = 0 := by
  apply chainBasis.repr.injective
  apply Finsupp.ext
  intro s
  simp only [map_zero, Finsupp.zero_apply]
  by_contra hs
  have hcount : qCount s = q := by
    by_contra hne
    exact hs (by simp [repr_qPart, hne])
  have hnonempty : (s.filter (fun i => i.isRight = true)).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < qCount s
    omega
  obtain ⟨i, himem⟩ := hnonempty
  obtain ⟨hi, hiright⟩ := Finset.mem_filter.mp himem
  cases i with
  | inl i => simp [Sum.isRight] at hiright
  | inr h =>
    have hh : h ∈ qSupport (qPart q x) :=
      (mem_qSupport_iff _ h).mpr ⟨s, hs, hi⟩
    simp [hsupport] at hh

/-- Every nonzero expression has a nonzero component of finite Q-degree. -/
theorem exists_qPart_ne_zero {x : A} (hx : x ≠ 0) : ∃ q, qPart q x ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  apply chainBasis.repr.injective
  apply Finsupp.ext
  intro s
  have hs := congrArg (fun a => chainBasis.repr a s) (h (qCount s))
  simpa using hs

/-- ET-09: a universal cycle whose coefficients contain no v-variables and
whose Q=0 specialization is zero must itself vanish. The proof uses the
least nonzero Q-degree and then the largest Q-index at that degree. -/
theorem noV_cycle_eq_zero (N m : ℕ) (hN : 0 < N) (hm : 0 < m)
    (x : A) (hx : NoV x) (hd : d N m x = 0) (hQ : eraseQ x = 0) : x = 0 := by
  classical
  by_contra hne
  have hex := exists_qPart_ne_zero hne
  let q := Nat.find hex
  have hqne : qPart q x ≠ 0 := Nat.find_spec hex
  have hqpos : 0 < q := by
    by_contra hpos
    have hqzero : q = 0 := by omega
    exact hqne (by rw [hqzero, ← eraseQ_eq_qPart_zero, hQ])
  have hprev : qPart (q - 1) x = 0 := by
    by_contra hprev
    have hle : q ≤ q - 1 := Nat.find_min' hex hprev
    omega
  have hcycle : dQ N m (qPart q x) = 0 := by
    have heq := congrArg (qPart (q - 1)) hd
    rw [d_eq_add, map_add, qPart_dA, qPart_dQ, hprev, map_zero, zero_add, map_zero] at heq
    have hindex : q - 1 + 1 = q := by omega
    simpa [hindex] using heq
  exact hqne (qPart_eq_zero_of_qSupport_eq_empty q hqpos x
    (qSupport_eq_empty_of_dQ N m hN hm _ (hx.qPart q) hcycle))

@[simp] theorem vDerivative_one (h : ℕ) : vDerivative h 1 = 0 := by
  rw [← chainBasis_empty, vDerivative_basis]

@[simp] theorem vDerivative_oddA (h i : ℕ) : vDerivative h (oddA i) = 0 := by
  rw [← chainBasis_singleton_A, vDerivative_basis]

@[simp] theorem vDerivative_oddQ (h i : ℕ) : vDerivative h (oddQ i) = 0 := by
  rw [← chainBasis_singleton_Q, vDerivative_basis]

/-- Coefficient differentiation is a derivation of the full exterior algebra. -/
theorem vDerivative_mul (h : ℕ) (x z : A) :
    vDerivative h (x * z) = vDerivative h x * z + x * vDerivative h z := by
  induction x using induction_on_generators with
  | hone => simp
  | hadd a b ha hb => simp only [add_mul, map_add, ha, hb]; abel
  | hsmul c a ha =>
    rw [smul_mul_assoc, vDerivative_smul, ha, vDerivative_smul]
    simp only [smul_add, add_mul, smul_mul_assoc, add_assoc]
  | hodd i a ha =>
    rw [mul_assoc, vDerivative_odd_mul, ha, vDerivative_odd_mul]
    simp only [mul_add, mul_assoc]

@[simp] theorem vDerivative_algebraMap (h : ℕ) (c : R) :
    vDerivative h (algebraMap R A c) = algebraMap R A (MvPolynomial.pderiv (Sum.inr h) c) := by
  rw [Algebra.algebraMap_eq_smul_one, vDerivative_smul, vDerivative_one, smul_zero, add_zero]
  exact (Algebra.algebraMap_eq_smul_one _).symm

@[simp] theorem noV_zero : NoV (0 : A) := fun _h => map_zero _
@[simp] theorem noV_one : NoV (1 : A) := vDerivative_one
@[simp] theorem noV_oddA (i : ℕ) : NoV (oddA i) := fun h => vDerivative_oddA h i
@[simp] theorem noV_oddQ (i : ℕ) : NoV (oddQ i) := fun h => vDerivative_oddQ h i

theorem NoV.add {x z : A} (hx : NoV x) (hz : NoV z) : NoV (x + z) := by
  intro h
  rw [map_add, hx h, hz h, add_zero]

theorem NoV.neg {x : A} (hx : NoV x) : NoV (-x) := by
  intro h
  rw [map_neg, hx h, neg_zero]

theorem NoV.sub {x z : A} (hx : NoV x) (hz : NoV z) : NoV (x - z) := by
  simpa [sub_eq_add_neg] using hx.add hz.neg

theorem NoV.mul {x z : A} (hx : NoV x) (hz : NoV z) : NoV (x * z) := by
  intro h
  rw [vDerivative_mul, hx h, hz h, zero_mul, mul_zero, add_zero]

theorem NoV.smul {x : A} (hx : NoV x) (c : R)
    (hc : ∀ h, MvPolynomial.pderiv (Sum.inr h) c = 0) : NoV (c • x) := by
  intro h
  rw [vDerivative_smul, hc h, hx h, zero_smul, smul_zero, add_zero]

theorem noV_algebraMap {c : R}
    (hc : ∀ h, MvPolynomial.pderiv (Sum.inr h) c = 0) : NoV (algebraMap R A c) := by
  intro h
  rw [vDerivative_algebraMap, hc h, map_zero]

@[simp] theorem noV_y (i : ℕ) : NoV (algebraMap R A (y i)) := by
  apply noV_algebraMap
  intro h
  simp [y]

@[simp] theorem noV_rat (c : ℚ) : NoV (algebraMap ℚ A c) := by
  rw [IsScalarTower.algebraMap_apply ℚ R A]
  apply noV_algebraMap
  intro h
  exact MvPolynomial.pderiv_C

theorem NoV.rat_smul {x : A} (hx : NoV x) (c : ℚ) : NoV (c • x) := by
  rw [Algebra.smul_def]
  exact (noV_rat c).mul hx

/-- The rational subalgebra of expressions whose even coefficients have
zero derivative in every v-variable. This supplies the closure interface
for all universal expressions built from y, A, and Q. -/
def noVSubalgebra : Subalgebra ℚ A where
  carrier := {x | NoV x}
  zero_mem' := noV_zero
  one_mem' := noV_one
  add_mem' := NoV.add
  mul_mem' := NoV.mul
  algebraMap_mem' := noV_rat

@[simp] theorem mem_noVSubalgebra (x : A) : x ∈ noVSubalgebra ↔ NoV x := Iff.rfl

end TorusLinkHomology.UniversalTransfer
