import TorusLinkHomology.HilbertSeries.GradedHomology

/-! Multiplicative and differential compatibility of the homogeneous chain spaces. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries
open CoordinateKoszul

theorem rationalChainBasis_mem (N n : ℕ) (m : ChainIndex n) :
    rationalChainBasis n m ∈ chainPiece N n
      (monomialDegree N m).1 (monomialDegree N m).2.1 (monomialDegree N m).2.2 := by
  rw [chainPiece_eq_span_degree]
  exact Submodule.subset_span ⟨m, rfl, rfl⟩

private theorem monomialDegree_add {N n : ℕ} (m t : ChainIndex n)
    (hd : Disjoint m.2 t.2) :
    monomialDegree N (m.1 + t.1, m.2 ∪ t.2) =
      ((monomialDegree N m).1 + (monomialDegree N t).1,
       (monomialDegree N m).2.1 + (monomialDegree N t).2.1,
       (monomialDegree N m).2.2 + (monomialDegree N t).2.2) := by
  classical
  simp only [monomialDegree, Finsupp.add_apply, Finset.sum_add_distrib,
    Nat.mul_add, Finset.card_union_of_disjoint hd, Finset.sum_union hd]
  apply Prod.ext
  · ring
  · apply Prod.ext
    · ring
    · rfl

private theorem rationalChainBasis_mul_mem (N n : ℕ) (m t : ChainIndex n) :
    rationalChainBasis n m * rationalChainBasis n t ∈
      chainPiece N n ((monomialDegree N m).1 + (monomialDegree N t).1)
        ((monomialDegree N m).2.1 + (monomialDegree N t).2.1)
        ((monomialDegree N m).2.2 + (monomialDegree N t).2.2) := by
  classical
  let b : Module.Basis (Fin n) (R n) (V n) := Finsupp.basisSingleOne
  let S : Set.powersetCard (Fin n) m.2.card := Set.powersetCard.ofCard rfl
  let T : Set.powersetCard (Fin n) t.2.card := Set.powersetCard.ofCard rfl
  rw [rationalChainBasis_apply, rationalChainBasis_apply, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  by_cases hd : Disjoint m.2 t.2
  · have hb := ExteriorAlgebra.basis_mul_of_disjoint b S T hd
    change chainBasis n m.2 * chainBasis n t.2 = _ at hb
    rw [hb, MvPolynomial.monomial_mul, one_mul]
    rw [smul_comm]
    have hm := rationalChainBasis_mem N n (m.1 + t.1, m.2 ∪ t.2)
    rw [monomialDegree_add m t hd] at hm
    have hu := (chainPiece N n _ _ _).smul_of_tower_mem
      (Set.powersetCard.permOfDisjoint (s := S) (t := T) hd).sign hm
    simpa only [rationalChainBasis_apply, chainBasis, b, S, T,
      Set.powersetCard.disjUnion, Set.powersetCard.ofCard, Finset.disjUnion_eq_union] using hu
  · have hb := ExteriorAlgebra.basis_mul_of_not_disjoint b S T hd
    change chainBasis n m.2 * chainBasis n t.2 = 0 at hb
    rw [hb, smul_zero]
    exact Submodule.zero_mem _

/-- Multiplication adds all three degrees. -/
theorem mul_mem_chainPiece {N n a b h a' b' h' : ℕ} {x y : A n}
    (hx : x ∈ chainPiece N n a b h) (hy : y ∈ chainPiece N n a' b' h') :
    x * y ∈ chainPiece N n (a + a') (b + b') (h + h') := by
  rw [chainPiece_eq_span_degree] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    change monomialDegree N m = (a, b, h) at hm
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨t, ht, rfl⟩ := hy
      change monomialDegree N t = (a', b', h') at ht
      simpa only [hm, ht] using rationalChainBasis_mul_mem N n m t
    | zero => simpa only [mul_zero] using (chainPiece N n (a + a') (b + b') (h + h')).zero_mem
    | add y z hy hz ihy ihz => simpa [mul_add] using Submodule.add_mem _ ihy ihz
    | smul r y hy ihy => simpa only [mul_smul_comm] using Submodule.smul_mem _ r ihy
  | zero => simpa only [zero_mul] using (chainPiece N n (a + a') (b + b') (h + h')).zero_mem
  | add x z hx hz ihx ihz => simpa [add_mul] using Submodule.add_mem _ ihx ihz
  | smul r x hx ihx => simpa only [smul_mul_assoc] using Submodule.smul_mem _ r ihx

theorem one_mem_chainPiece (N n : ℕ) : (1 : A n) ∈ chainPiece N n 0 0 0 := by
  simpa [monomialDegree] using rationalChainBasis_mem N n (0, ∅)

theorem polynomialMonomial_mem (N n : ℕ) (m : Fin n →₀ ℕ) :
    algebraMap (R n) (A n) (MvPolynomial.monomial m (1 : ℚ)) ∈
      chainPiece N n (∑ i : Fin n, m i) (∑ i : Fin n, i.val * m i) 0 := by
  simpa [monomialDegree, rationalChainBasis_apply, Algebra.smul_def] using
    rationalChainBasis_mem N n (m, ∅)

theorem u_mem_chainPiece (N n : ℕ) (i : Fin n) :
    algebraMap (R n) (A n) (u n i) ∈ chainPiece N n 1 i.val 0 := by
  classical
  simpa [u, MvPolynomial.X, Finsupp.single_apply, Finset.sum_ite_eq',
    Finset.sum_ite_eq] using polynomialMonomial_mem N n (Finsupp.single i 1)

theorem xi_mem_chainPiece (N n : ℕ) (i : Fin n) :
    xi n i ∈ chainPiece N n N i.val 1 := by
  simpa [monomialDegree, rationalChainBasis_apply] using
    rationalChainBasis_mem N n (0, {i})

private theorem uPolynomial_coeff_mem (N n k : ℕ) :
    algebraMap (R n) (A n) ((uPolynomial n).coeff k) ∈ chainPiece N n 1 k 0 := by
  classical
  simp only [uPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, map_sum]
  apply Submodule.sum_mem
  intro i hi
  split_ifs with hik
  · subst k
    exact u_mem_chainPiece N n i
  · simp

/-- Coefficients of powers of the jet polynomial carry their expected two degrees. -/
theorem uPolynomial_pow_coeff_mem (N n e k : ℕ) :
    algebraMap (R n) (A n) (((uPolynomial n) ^ e).coeff k) ∈
      chainPiece N n e k 0 := by
  classical
  induction e generalizing k with
  | zero =>
    simp only [pow_zero, Polynomial.coeff_one]
    split_ifs with hk
    · subst k; simpa using one_mem_chainPiece N n
    · simp
  | succ e ih =>
    rw [pow_succ, Polynomial.coeff_mul, map_sum]
    apply Submodule.sum_mem
    intro p hp
    rw [map_mul]
    have hm := mul_mem_chainPiece (ih p.1) (uPolynomial_coeff_mem N n p.2)
    have hsum := Finset.mem_antidiagonal.mp hp
    simpa only [hsum, Nat.add_zero] using hm

/-- The equations defining the Koszul differential have degree (N,i,0). -/
theorem differentialCoefficient_mem (N n : ℕ) (i : Fin n) :
    algebraMap (R n) (A n) (differentialCoefficient N n i) ∈ chainPiece N n N i.val 0 :=
  uPolynomial_pow_coeff_mem N n N i.val

theorem chainBasis_mem_chainPiece (N n : ℕ) (s : Finset (Fin n)) :
    chainBasis n s ∈ chainPiece N n (N * s.card) (∑ i ∈ s, i.val) s.card := by
  simpa [monomialDegree, rationalChainBasis_apply] using rationalChainBasis_mem N n (0, s)

theorem chainBasis_insert_eq_unit_smul (n : ℕ) (i : Fin n)
    (s : Finset (Fin n)) (hi : i ∉ s) :
    ∃ c : ℤˣ, chainBasis n (insert i s) = c • (xi n i * chainBasis n s) := by
  classical
  let b : Module.Basis (Fin n) (R n) (V n) := Finsupp.basisSingleOne
  let S : Set.powersetCard (Fin n) 1 := Set.powersetCard.ofCard (Finset.card_singleton i)
  let T : Set.powersetCard (Fin n) s.card := Set.powersetCard.ofCard rfl
  have hd : Disjoint S.val T.val := Finset.disjoint_singleton_left.mpr hi
  let c := (Set.powersetCard.permOfDisjoint hd).sign
  have he : xi n i * chainBasis n s = c • chainBasis n (insert i s) := by
    have hb := ExteriorAlgebra.basis_mul_of_disjoint b S T hd
    change chainBasis n S.val * chainBasis n T.val =
      c • chainBasis n (Set.powersetCard.disjUnion hd).val at hb
    simpa only [S, T, Set.powersetCard.ofCard, Set.powersetCard.disjUnion,
      Finset.disjUnion_eq_union, Finset.singleton_union, chainBasis_singleton] using hb
  refine ⟨c⁻¹, ?_⟩
  rw [he, inv_smul_smul]

/-- On an exterior basis vector the differential lowers exterior degree by one
and preserves the other two degrees. The empty exterior vector maps to zero. -/
theorem d_chainBasis_mem (N n : ℕ) (s : Finset (Fin n)) :
    d N n (chainBasis n s) ∈
      chainPiece N n (N * s.card) (∑ i ∈ s, i.val) (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [d]
  | @insert i s hi ih =>
    by_cases hs : s = ∅
    · subst s
      simpa using differentialCoefficient_mem N n i
    · obtain ⟨c, hc⟩ := chainBasis_insert_eq_unit_smul n i s hi
      rw [hc, Units.smul_def, map_zsmul]
      apply Submodule.smul_of_tower_mem
      rw [d_xi_mul]
      apply Submodule.sub_mem
      · have hm := mul_mem_chainPiece (differentialCoefficient_mem N n i)
          (chainBasis_mem_chainPiece N n s)
        simpa only [Algebra.smul_def, Finset.card_insert_of_notMem hi,
          Finset.sum_insert hi, Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one,
          Nat.zero_add, Nat.add_zero, Nat.add_comm] using hm
      · have hm := mul_mem_chainPiece (xi_mem_chainPiece N n i) ih
        have hc : 1 + (s.card - 1) = s.card := by
          have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
          omega
        simpa only [Finset.card_insert_of_notMem hi, Finset.sum_insert hi,
          Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one, hc, Nat.add_comm] using hm

/-- The trigrading is compatible with the differential, including its value
zero on exterior degree zero. -/
theorem d_mem_chainPiece {N n a b h : ℕ} {x : A n}
    (hx : x ∈ chainPiece N n a b h) : d N n x ∈ chainPiece N n a b (h - 1) := by
  rw [chainPiece_eq_span_degree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    change monomialDegree N m = (a, b, h) at hm
    have hd := mul_mem_chainPiece (polynomialMonomial_mem N n m.1) (d_chainBasis_mem N n m.2)
    have ha := congrArg Prod.fst hm
    have hb := congrArg (fun d => d.2.1) hm
    have hh := congrArg (fun d => d.2.2) hm
    change (∑ i : Fin n, m.1 i) + N * m.2.card = a at ha
    change (∑ i : Fin n, i.val * m.1 i) + (∑ i ∈ m.2, i.val) = b at hb
    change m.2.card = h at hh
    rw [rationalChainBasis_apply, map_smul, Algebra.smul_def]
    rw [ha, hb, Nat.zero_add, hh] at hd
    exact hd
  | zero => simp
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul r x hx ihx => simpa only [map_rat_smul] using Submodule.smul_mem _ r ihx

theorem homogeneousProjection_eq_zero_of_mem {N n a b h a' b' h' : ℕ} {x : A n}
    (hx : x ∈ chainPiece N n a b h) (hne : (a, b, h) ≠ (a', b', h')) :
    homogeneousProjection N n a' b' h' x = 0 := by
  classical
  apply (rationalChainBasis n).repr.injective
  ext m
  rw [repr_homogeneousProjection, map_zero, Finsupp.zero_apply]
  by_cases hm : m ∈ ((rationalChainBasis n).repr x).support
  · have hd := (mem_chainPiece_iff N n a b h x).mp hx m hm
    rw [hd, if_neg hne]
  · simp [Finsupp.notMem_support_iff.mp hm]

/-- A projection in the target is obtained by projecting the primitive one
exterior degree higher. -/
theorem homogeneousProjection_d (N n a b h : ℕ) (x : A n) :
    homogeneousProjection N n a b h (d N n x) =
      d N n (homogeneousProjection N n a b (h + 1) x) := by
  have he : (homogeneousProjection N n a b h).comp ((d N n).restrictScalars ℚ) =
      ((d N n).restrictScalars ℚ).comp (homogeneousProjection N n a b (h + 1)) := by
    apply (rationalChainBasis n).ext
    intro m
    change homogeneousProjection N n a b h (d N n (rationalChainBasis n m)) =
      d N n (homogeneousProjection N n a b (h + 1) (rationalChainBasis n m))
    rw [homogeneousProjection_basis]
    have hm := rationalChainBasis_mem N n m
    by_cases hh : (monomialDegree N m).2.2 = 0
    · have hd : d N n (rationalChainBasis n m) = 0 :=
        d_eq_zero_of_mem_chainPiece_zero (hh ▸ hm)
      have hn : monomialDegree N m ≠ (a, b, h + 1) := by
        intro he
        have heh : (monomialDegree N m).2.2 = h + 1 := congrArg (fun d => d.2.2) he
        omega
      rw [hd, if_neg hn, map_zero, map_zero]
    · have hd := d_mem_chainPiece hm
      by_cases he : monomialDegree N m = (a, b, h + 1)
      · rw [if_pos he]
        apply homogeneousProjection_eq_self
        simpa only [he, Nat.add_sub_cancel] using hd
      · rw [if_neg he, map_zero]
        apply homogeneousProjection_eq_zero_of_mem hd
        intro he'
        apply he
        have ha : (monomialDegree N m).1 = a := congrArg (fun d => d.1) he'
        have hb : (monomialDegree N m).2.1 = b := congrArg (fun d => d.2.1) he'
        have heh : (monomialDegree N m).2.2 - 1 = h := congrArg (fun d => d.2.2) he'
        have hh' : (monomialDegree N m).2.2 = h + 1 := by omega
        exact Prod.ext ha (Prod.ext hb hh')
  exact LinearMap.congr_fun he x

/-- Every homogeneous boundary has a homogeneous primitive of the required
next exterior degree, even if its original primitive is inhomogeneous. -/
theorem exists_homogeneous_primitive {N n a b h : ℕ} {x : A n}
    (hx : x ∈ chainPiece N n a b h) (hb : ∃ y : A n, d N n y = x) :
    ∃ y ∈ chainPiece N n a b (h + 1), d N n y = x := by
  obtain ⟨y, rfl⟩ := hb
  refine ⟨homogeneousProjection N n a b (h + 1) y, homogeneousProjection_mem _ _ _ _ _ _, ?_⟩
  rw [← homogeneousProjection_d]
  exact homogeneousProjection_eq_self hx

/-- Homogeneous boundaries are homogeneous cycles. -/
theorem boundaryPiece_le_cyclePiece (N n a b h : ℕ) :
    boundaryPiece N n a b h ≤ cyclePiece N n a b h := by
  rintro z ⟨y, rfl⟩
  change d N n y.val ∈ chainPiece N n a b h
  simpa only [Nat.add_sub_cancel] using d_mem_chainPiece y.property

/-- Vanishing of a homogeneous cycle class is exactly membership in the image
from the next homogeneous chain space. -/
theorem cycleClass_eq_zero_iff_mem_boundaryPiece {N n a b h : ℕ}
    (x : cyclePiece N n a b h) :
    cycleClassMap N n a b h x = 0 ↔ x.val ∈ boundaryPiece N n a b h := by
  change (torusLinkDGA N n).homologyClass x.val = 0 ↔ _
  rw [(torusLinkDGA N n).homologyClass_eq_zero_iff]
  constructor
  · intro hb
    obtain ⟨y, hy, he⟩ := exists_homogeneous_primitive x.property hb
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  · rintro ⟨y, hy⟩
    exact ⟨y.val, congrArg Subtype.val hy⟩

/-- The null-class subspace and the homogeneous boundary space are the same
vector space, with their different ambient subtypes made explicit. -/
def cycleClassKerEquivBoundary (N n a b h : ℕ) :
    LinearMap.ker (cycleClassMap N n a b h) ≃ₗ[ℚ] boundaryPiece N n a b h where
  toFun x := ⟨x.val.val, (cycleClass_eq_zero_iff_mem_boundaryPiece x.val).mp x.property⟩
  invFun x := ⟨⟨x.val, boundaryPiece_le_cyclePiece N n a b h x.property⟩,
    (cycleClass_eq_zero_iff_mem_boundaryPiece _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_cycleClassMap_eq (N n a b h : ℕ) :
    LinearMap.ker (cycleClassMap N n a b h) =
      (boundaryPiece N n a b h).comap (cyclePiece N n a b h).subtype := by
  ext x
  exact cycleClass_eq_zero_iff_mem_boundaryPiece x

/-- The existing homogeneous homology piece is the quotient of homogeneous
cycles by the boundaries having homogeneous primitives. -/
def homogeneousHomologyQuotientEquiv (N n a b h : ℕ) :
    (cyclePiece N n a b h ⧸
      (boundaryPiece N n a b h).comap (cyclePiece N n a b h).subtype) ≃ₗ[ℚ]
      homologyPiece N n a b h := by
  rw [← ker_cycleClassMap_eq, ← range_cycleClassMap]
  exact (cycleClassMap N n a b h).quotKerEquivRange

/-- The required dimension identity for homogeneous cycles and boundaries. -/
theorem finrank_cyclePiece_eq_homology_add_boundary (N n a b h : ℕ) :
    Module.finrank ℚ (cyclePiece N n a b h) = homologyDimension N n a b h +
      Module.finrank ℚ (boundaryPiece N n a b h) := by
  rw [finrank_cyclePiece, (cycleClassKerEquivBoundary N n a b h).finrank_eq]

end TorusLinkHomology.HilbertSeries
