import TorusLinkHomology.HilbertSeries.GradedDifferential
import TorusLinkHomology.HilbertSeries.AuxiliaryRecurrence

/-! Positive weight spaces in the auxiliary coefficient Koszul complexes.
Polynomial generators have weights i+1; exterior generators at offset ell
have weights ell+i+1. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries.Auxiliary
open CoordinateKoszul

/-- Weight and exterior degree of an auxiliary rational basis vector. -/
def monomialDegree (ell : ℕ) {r : ℕ} (m : ChainIndex r) : ℕ × ℕ :=
  ((∑ i : Fin r, (i.val + 1) * m.1 i) + (∑ i ∈ m.2, (ell + i.val + 1)), m.2.card)

/-- Bounded indices of the auxiliary homogeneous basis. -/
def HasDegree (ell r w h : ℕ) (m : BoundedMonomial r w) : Prop :=
  (∑ i : Fin r, (i.val + 1) * (m.1 i).val) + (∑ i ∈ m.2, (ell + i.val + 1)) = w ∧
    m.2.card = h

def chainPiece (ell r w h : ℕ) : Submodule ℚ (A r) :=
  Submodule.span ℚ (Set.range fun m : {m : BoundedMonomial r w // HasDegree ell r w h m} =>
    chainMonomial r w m.val)

instance chainPiece_finiteDimensional (ell r w h : ℕ) :
    FiniteDimensional ℚ (chainPiece ell r w h) := by
  unfold chainPiece
  exact FiniteDimensional.span_of_finite ℚ (Set.finite_range _)

/-- The homogeneous pieces of the actual auxiliary cycle algebra. -/
def cyclePiece (N ell r w h : ℕ) : Submodule ℚ (CoefficientComplex.dga N r ell).cycles :=
  (chainPiece ell r w h).comap
    ((CoefficientComplex.dga N r ell).cycles.val.toLinearMap.restrictScalars ℚ)

instance cyclePiece_finiteDimensional (N ell r w h : ℕ) :
    FiniteDimensional ℚ (cyclePiece N ell r w h) := by
  let f : cyclePiece N ell r w h →ₗ[ℚ] chainPiece ell r w h :=
    { toFun x := ⟨x.val.val, x.property⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  apply FiniteDimensional.of_injective f
  intro x y he
  exact Subtype.ext (Subtype.ext (congrArg (fun z : chainPiece ell r w h => z.val) he))

/-- Homogeneous homology is the image in the actual auxiliary homology. -/
def homologyPiece (N ell r w h : ℕ) : Submodule ℚ (CoefficientComplex.dga N r ell).Homology :=
  (cyclePiece N ell r w h).map
    ((CoefficientComplex.dga N r ell).homologyClass.toLinearMap.restrictScalars ℚ)

instance homologyPiece_finiteDimensional (N ell r w h : ℕ) :
    FiniteDimensional ℚ (homologyPiece N ell r w h) := by
  unfold homologyPiece
  infer_instance

def homologyDimension (N ell r w h : ℕ) : ℕ :=
  Module.finrank ℚ (homologyPiece N ell r w h)

/-- The exponent cutoff by w loses no monomials because all weights are positive. -/
theorem chainPiece_eq_span_degree (ell r w h : ℕ) :
    chainPiece ell r w h = Submodule.span ℚ
      ((rationalChainBasis r) '' {m : ChainIndex r | monomialDegree ell m = (w, h)}) := by
  unfold chainPiece
  congr 1
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨(Finsupp.equivFunOnFinite.symm (fun i => (m.val.1 i).val), m.val.2), ?_, rfl⟩
    exact Prod.ext m.property.1 m.property.2
  · rintro ⟨m, hm, rfl⟩
    have hw : (∑ i : Fin r, (i.val + 1) * m.1 i) + (∑ i ∈ m.2, (ell + i.val + 1)) = w :=
      congrArg Prod.fst hm
    have hi (i : Fin r) : m.1 i < w + 1 := by
      have hs := Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) => Nat.zero_le ((j.val + 1) * m.1 j))
        (Finset.mem_univ i)
      have hp : m.1 i ≤ (i.val + 1) * m.1 i := le_mul_of_one_le_left (Nat.zero_le _) (by omega)
      omega
    let mb : BoundedMonomial r w := (fun i => ⟨m.1 i, hi i⟩, m.2)
    have hmb : HasDegree ell r w h mb := ⟨hw, congrArg Prod.snd hm⟩
    refine ⟨⟨mb, hmb⟩, ?_⟩
    apply congrArg (rationalChainBasis r)
    apply Prod.ext
    · ext i; simp [mb]
    · rfl

theorem mem_chainPiece_iff (ell r w h : ℕ) (x : A r) :
    x ∈ chainPiece ell r w h ↔ ∀ m ∈ ((rationalChainBasis r).repr x).support,
      monomialDegree ell m = (w, h) := by
  rw [chainPiece_eq_span_degree, (rationalChainBasis r).mem_span_image]
  rfl

/-- Projection onto an auxiliary weight and exterior degree. -/
def homogeneousProjection (ell r w h : ℕ) : A r →ₗ[ℚ] A r := by
  classical
  exact (rationalChainBasis r).rationalDiagonal
    (fun m => if monomialDegree ell m = (w, h) then 1 else 0)

@[simp] theorem homogeneousProjection_basis (ell r w h : ℕ) (m : ChainIndex r) :
    homogeneousProjection ell r w h (rationalChainBasis r m) =
      if monomialDegree ell m = (w, h) then rationalChainBasis r m else 0 := by
  classical
  simp only [homogeneousProjection, Module.Basis.rationalDiagonal_basis]
  split_ifs <;> simp

@[simp] theorem repr_homogeneousProjection (ell r w h : ℕ) (x : A r) (m : ChainIndex r) :
    (rationalChainBasis r).repr (homogeneousProjection ell r w h x) m =
      if monomialDegree ell m = (w, h) then (rationalChainBasis r).repr x m else 0 := by
  classical
  simp only [homogeneousProjection, Module.Basis.repr_rationalDiagonal]
  split_ifs <;> simp

theorem homogeneousProjection_mem (ell r w h : ℕ) (x : A r) :
    homogeneousProjection ell r w h x ∈ chainPiece ell r w h := by
  classical
  rw [mem_chainPiece_iff]
  intro m hm
  by_contra hd
  simp [Finsupp.mem_support_iff, hd] at hm

theorem homogeneousProjection_eq_self {ell r w h : ℕ} {x : A r}
    (hx : x ∈ chainPiece ell r w h) : homogeneousProjection ell r w h x = x := by
  classical
  apply (rationalChainBasis r).repr.injective
  ext m
  rw [repr_homogeneousProjection]
  by_cases hm : m ∈ ((rationalChainBasis r).repr x).support
  · rw [if_pos ((mem_chainPiece_iff ell r w h x).mp hx m hm)]
  · simp [Finsupp.notMem_support_iff.mp hm]

theorem homogeneousProjection_eq_zero_of_mem {ell r w h w' h' : ℕ} {x : A r}
    (hx : x ∈ chainPiece ell r w h) (hne : (w, h) ≠ (w', h')) :
    homogeneousProjection ell r w' h' x = 0 := by
  classical
  apply (rationalChainBasis r).repr.injective
  ext m
  rw [repr_homogeneousProjection, map_zero, Finsupp.zero_apply]
  by_cases hm : m ∈ ((rationalChainBasis r).repr x).support
  · have hd := (mem_chainPiece_iff ell r w h x).mp hx m hm
    rw [hd, if_neg hne]
  · simp [Finsupp.notMem_support_iff.mp hm]

/-- Each chain has a finite decomposition into auxiliary homogeneous pieces. -/
theorem sum_homogeneousProjection (ell r : ℕ) (x : A r) :
    ∑ d ∈ ((rationalChainBasis r).repr x).support.image (monomialDegree ell),
      homogeneousProjection ell r d.1 d.2 x = x := by
  classical
  apply (rationalChainBasis r).repr.injective
  ext m
  simp only [map_sum, Finsupp.finsetSum_apply, repr_homogeneousProjection, Prod.eta]
  by_cases hm : m ∈ ((rationalChainBasis r).repr x).support
  · have hd := Finset.mem_image_of_mem (monomialDegree ell) hm
    simp only [Finset.sum_ite_eq, if_pos hd]
  · simp [Finsupp.notMem_support_iff.mp hm]

theorem rationalChainBasis_mem (ell r : ℕ) (m : ChainIndex r) :
    rationalChainBasis r m ∈ chainPiece ell r (monomialDegree ell m).1 (monomialDegree ell m).2 := by
  rw [chainPiece_eq_span_degree]
  exact Submodule.subset_span ⟨m, rfl, rfl⟩

private theorem monomialDegree_add {ell r : ℕ} (m t : ChainIndex r)
    (hd : Disjoint m.2 t.2) :
    monomialDegree ell (m.1 + t.1, m.2 ∪ t.2) =
      ((monomialDegree ell m).1 + (monomialDegree ell t).1,
       (monomialDegree ell m).2 + (monomialDegree ell t).2) := by
  classical
  simp only [monomialDegree, Finsupp.add_apply, Finset.sum_add_distrib,
    Nat.mul_add, Finset.card_union_of_disjoint hd, Finset.sum_union hd]
  apply Prod.ext
  · ring
  · rfl

private theorem rationalChainBasis_mul_mem (ell r : ℕ) (m t : ChainIndex r) :
    rationalChainBasis r m * rationalChainBasis r t ∈
      chainPiece ell r ((monomialDegree ell m).1 + (monomialDegree ell t).1)
        ((monomialDegree ell m).2 + (monomialDegree ell t).2) := by
  classical
  let b : Module.Basis (Fin r) (R r) (V r) := Finsupp.basisSingleOne
  let S : Set.powersetCard (Fin r) m.2.card := Set.powersetCard.ofCard rfl
  let T : Set.powersetCard (Fin r) t.2.card := Set.powersetCard.ofCard rfl
  rw [rationalChainBasis_apply, rationalChainBasis_apply, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  by_cases hd : Disjoint m.2 t.2
  · have hb := ExteriorAlgebra.basis_mul_of_disjoint b S T hd
    change chainBasis r m.2 * chainBasis r t.2 = _ at hb
    rw [hb, MvPolynomial.monomial_mul, one_mul, smul_comm]
    have hm := rationalChainBasis_mem ell r (m.1 + t.1, m.2 ∪ t.2)
    rw [monomialDegree_add m t hd] at hm
    have hu := (chainPiece ell r _ _).smul_of_tower_mem
      (Set.powersetCard.permOfDisjoint (s := S) (t := T) hd).sign hm
    simpa only [rationalChainBasis_apply, chainBasis, b, S, T,
      Set.powersetCard.disjUnion, Set.powersetCard.ofCard, Finset.disjUnion_eq_union] using hu
  · have hb := ExteriorAlgebra.basis_mul_of_not_disjoint b S T hd
    change chainBasis r m.2 * chainBasis r t.2 = 0 at hb
    rw [hb, smul_zero]
    exact Submodule.zero_mem _

theorem mul_mem_chainPiece {ell r w h w' h' : ℕ} {x y : A r}
    (hx : x ∈ chainPiece ell r w h) (hy : y ∈ chainPiece ell r w' h') :
    x * y ∈ chainPiece ell r (w + w') (h + h') := by
  rw [chainPiece_eq_span_degree] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    change monomialDegree ell m = (w, h) at hm
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨t, ht, rfl⟩ := hy
      change monomialDegree ell t = (w', h') at ht
      simpa only [hm, ht] using rationalChainBasis_mul_mem ell r m t
    | zero => simpa only [mul_zero] using (chainPiece ell r (w + w') (h + h')).zero_mem
    | add y z hy hz ihy ihz => simpa [mul_add] using Submodule.add_mem _ ihy ihz
    | smul q y hy ihy => simpa only [mul_smul_comm] using Submodule.smul_mem _ q ihy
  | zero => simpa only [zero_mul] using (chainPiece ell r (w + w') (h + h')).zero_mem
  | add x z hx hz ihx ihz => simpa [add_mul] using Submodule.add_mem _ ihx ihz
  | smul q x hx ihx => simpa only [smul_mul_assoc] using Submodule.smul_mem _ q ihx

theorem one_mem_chainPiece (ell r : ℕ) : (1 : A r) ∈ chainPiece ell r 0 0 := by
  simpa [monomialDegree] using rationalChainBasis_mem ell r (0, ∅)

theorem polynomialMonomial_mem (ell r : ℕ) (m : Fin r →₀ ℕ) :
    algebraMap (R r) (A r) (MvPolynomial.monomial m (1 : ℚ)) ∈
      chainPiece ell r (∑ i : Fin r, (i.val + 1) * m i) 0 := by
  simpa [monomialDegree, rationalChainBasis_apply, Algebra.smul_def] using
    rationalChainBasis_mem ell r (m, ∅)

theorem e_mem_chainPiece (ell r : ℕ) (i : Fin r) :
    algebraMap (R r) (A r) (CoefficientComplex.e r i) ∈ chainPiece ell r (i.val + 1) 0 := by
  classical
  simpa [CoefficientComplex.e, MvPolynomial.X, Finsupp.single_apply, Finset.sum_ite_eq',
    Finset.sum_ite_eq] using polynomialMonomial_mem ell r (Finsupp.single i 1)

theorem xi_mem_chainPiece (ell r : ℕ) (i : Fin r) :
    CoefficientComplex.xi r i ∈ chainPiece ell r (ell + i.val + 1) 1 := by
  simpa [monomialDegree, rationalChainBasis_apply, CoefficientComplex.xi, xi] using
    rationalChainBasis_mem ell r (0, {i})

private theorem E_coeff_mem (ell r k : ℕ) :
    algebraMap (R r) (A r) ((CoefficientComplex.E r).coeff k) ∈ chainPiece ell r k 0 := by
  classical
  simp only [CoefficientComplex.E, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, map_add, map_sum]
  apply Submodule.add_mem
  · simp only [Polynomial.coeff_one]
    split_ifs with hk
    · subst k; simpa using one_mem_chainPiece ell r
    · simp
  · apply Submodule.sum_mem
    intro i hi
    split_ifs with hik
    · subst k; exact e_mem_chainPiece ell r i
    · simp

/-- Every coefficient equation G_j is homogeneous of positive-generator weight j. -/
theorem G_mem_chainPiece (N ell r k : ℕ) :
    algebraMap (R r) (A r) (CoefficientComplex.G N r k) ∈ chainPiece ell r k 0 := by
  classical
  unfold CoefficientComplex.G
  induction N generalizing k with
  | zero =>
    simp only [pow_zero, Polynomial.coeff_one]
    split_ifs with hk
    · subst k; simpa using one_mem_chainPiece ell r
    · simp
  | succ N ih =>
    rw [pow_succ, Polynomial.coeff_mul, map_sum]
    apply Submodule.sum_mem
    intro p hp
    rw [map_mul]
    have hm := mul_mem_chainPiece (ih p.1) (E_coeff_mem ell r p.2)
    have hsum := Finset.mem_antidiagonal.mp hp
    simpa only [hsum, Nat.add_zero] using hm

theorem chainBasis_mem_chainPiece (ell r : ℕ) (s : Finset (Fin r)) :
    chainBasis r s ∈ chainPiece ell r (∑ i ∈ s, (ell + i.val + 1)) s.card := by
  simpa [monomialDegree, rationalChainBasis_apply] using rationalChainBasis_mem ell r (0, s)

private theorem d_xi_mul (N r ell : ℕ) (i : Fin r) (x : A r) :
    CoefficientComplex.d N r ell (xi r i * x) =
      CoefficientComplex.G N r (ell + i.val + 1) • x -
        xi r i * CoefficientComplex.d N r ell x := by
  simpa [CoefficientComplex.d, CoefficientComplex.dga, xi, CoefficientComplex.differentialFunctional]
    using CliffordAlgebra.contractLeft_ι_mul
      (Q := (0 : QuadraticForm (R r) (V r))) (CoefficientComplex.differentialFunctional N r ell)
      (Finsupp.single i 1) x

/-- The auxiliary differential preserves weight and lowers exterior degree. -/
theorem d_chainBasis_mem (N ell r : ℕ) (s : Finset (Fin r)) :
    CoefficientComplex.d N r ell (chainBasis r s) ∈
      chainPiece ell r (∑ i ∈ s, (ell + i.val + 1)) (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [CoefficientComplex.d, CoefficientComplex.dga]
  | @insert i s hi ih =>
    by_cases hs : s = ∅
    · subst s
      simpa [chainBasis_singleton, xi, CoefficientComplex.d, CoefficientComplex.dga,
        CoefficientComplex.differentialFunctional] using G_mem_chainPiece N ell r (ell + i.val + 1)
    · obtain ⟨c, hc⟩ := chainBasis_insert_eq_unit_smul r i s hi
      rw [hc, Units.smul_def, map_zsmul]
      apply Submodule.smul_of_tower_mem
      rw [d_xi_mul]
      apply Submodule.sub_mem
      · have hm := mul_mem_chainPiece (G_mem_chainPiece N ell r (ell + i.val + 1))
          (chainBasis_mem_chainPiece ell r s)
        simpa only [Algebra.smul_def, Finset.card_insert_of_notMem hi,
          Finset.sum_insert hi, Nat.add_sub_cancel, Nat.zero_add] using hm
      · have hm := mul_mem_chainPiece (xi_mem_chainPiece ell r i) ih
        have hc : 1 + (s.card - 1) = s.card := by
          have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
          omega
        simpa only [Finset.card_insert_of_notMem hi, Finset.sum_insert hi,
          Nat.add_sub_cancel, hc, CoefficientComplex.xi, xi] using hm

theorem d_mem_chainPiece {N ell r w h : ℕ} {x : A r}
    (hx : x ∈ chainPiece ell r w h) :
    CoefficientComplex.d N r ell x ∈ chainPiece ell r w (h - 1) := by
  rw [chainPiece_eq_span_degree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    change monomialDegree ell m = (w, h) at hm
    have hd := mul_mem_chainPiece (polynomialMonomial_mem ell r m.1) (d_chainBasis_mem N ell r m.2)
    have hw : (∑ i : Fin r, (i.val + 1) * m.1 i) +
        (∑ i ∈ m.2, (ell + i.val + 1)) = w := congrArg Prod.fst hm
    have hh : m.2.card = h := congrArg Prod.snd hm
    rw [rationalChainBasis_apply, map_smul, Algebra.smul_def]
    rw [hw, Nat.zero_add, hh] at hd
    exact hd
  | zero => simp
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul q x hx ihx => simpa only [map_rat_smul] using Submodule.smul_mem _ q ihx

theorem d_eq_zero_of_mem_chainPiece_zero {N ell r w : ℕ} {x : A r}
    (hx : x ∈ chainPiece ell r w 0) : CoefficientComplex.d N r ell x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    have hm : m.val.2 = ∅ := Finset.card_eq_zero.mp m.property.2
    simp [chainMonomial, rationalChainBasis_apply, hm, CoefficientComplex.d, CoefficientComplex.dga]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul q x hx ih => simp [map_rat_smul, ih]

/-- The auxiliary differential commutes with projection to matching weight. -/
theorem homogeneousProjection_d (N ell r w h : ℕ) (x : A r) :
    homogeneousProjection ell r w h (CoefficientComplex.d N r ell x) =
      CoefficientComplex.d N r ell (homogeneousProjection ell r w (h + 1) x) := by
  have he : (homogeneousProjection ell r w h).comp ((CoefficientComplex.d N r ell).restrictScalars ℚ) =
      ((CoefficientComplex.d N r ell).restrictScalars ℚ).comp (homogeneousProjection ell r w (h + 1)) := by
    apply (rationalChainBasis r).ext
    intro m
    change homogeneousProjection ell r w h (CoefficientComplex.d N r ell (rationalChainBasis r m)) =
      CoefficientComplex.d N r ell (homogeneousProjection ell r w (h + 1) (rationalChainBasis r m))
    rw [homogeneousProjection_basis]
    have hm := rationalChainBasis_mem ell r m
    by_cases hh : (monomialDegree ell m).2 = 0
    · have hd : CoefficientComplex.d N r ell (rationalChainBasis r m) = 0 :=
        d_eq_zero_of_mem_chainPiece_zero (hh ▸ hm)
      have hn : monomialDegree ell m ≠ (w, h + 1) := by
        intro he
        have heh : (monomialDegree ell m).2 = h + 1 := congrArg Prod.snd he
        omega
      rw [hd, if_neg hn, map_zero, map_zero]
    · have hd := d_mem_chainPiece (N := N) hm
      by_cases he : monomialDegree ell m = (w, h + 1)
      · rw [if_pos he]
        apply homogeneousProjection_eq_self
        simpa only [he, Nat.add_sub_cancel] using hd
      · rw [if_neg he, map_zero]
        apply homogeneousProjection_eq_zero_of_mem hd
        intro he'
        apply he
        have hw : (monomialDegree ell m).1 = w := congrArg Prod.fst he'
        have heh : (monomialDegree ell m).2 - 1 = h := congrArg Prod.snd he'
        have hh' : (monomialDegree ell m).2 = h + 1 := by omega
        exact Prod.ext hw hh'
  exact LinearMap.congr_fun he x

/-- An auxiliary homogeneous boundary admits a homogeneous primitive. -/
theorem exists_homogeneous_primitive {N ell r w h : ℕ} {x : A r}
    (hx : x ∈ chainPiece ell r w h) (hb : ∃ y : A r, CoefficientComplex.d N r ell y = x) :
    ∃ y ∈ chainPiece ell r w (h + 1), CoefficientComplex.d N r ell y = x := by
  obtain ⟨y, rfl⟩ := hb
  refine ⟨homogeneousProjection ell r w (h + 1) y, homogeneousProjection_mem _ _ _ _ _, ?_⟩
  rw [← homogeneousProjection_d]
  exact homogeneousProjection_eq_self hx

private theorem rationalCoefficient_smul_mem {ell r w h : ℕ} {x : A r}
    (q : ℚ) (hx : x ∈ chainPiece ell r w h) :
    (algebraMap ℚ (R r) q) • x ∈ chainPiece ell r w h := by
  simpa only [IsScalarTower.algebraMap_smul] using Submodule.smul_mem _ q hx

theorem chi_mem_chainPiece (ell r j : ℕ) :
    CoefficientComplex.chi r ell j ∈ chainPiece ell r j 1 := by
  classical
  unfold CoefficientComplex.chi
  split_ifs with hj
  · have he : ell + (j - ell - 1) + 1 = j := by omega
    simpa only [he] using xi_mem_chainPiece ell r ⟨j - ell - 1, by omega⟩
  · exact Submodule.zero_mem _

/-- The recursively extended generator with absolute index j has weight j. -/
theorem tail_mem_chainPiece (N ell r j : ℕ) :
    CoefficientComplex.tail N r ell j ∈ chainPiece ell r j 1 := by
  classical
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases htop : j ≤ ell + r
    · rw [CoefficientComplex.tail_eq_chi _ _ _ _ htop]
      exact chi_mem_chainPiece ell r j
    · have hgt : ell + r < j := by omega
      rw [CoefficientComplex.tail_eq_of_gt _ _ _ _ hgt]
      apply rationalCoefficient_smul_mem
      apply Submodule.sum_mem
      intro i hi
      have hm := mul_mem_chainPiece (e_mem_chainPiece ell r i)
        (ih (j - (i.val + 1)) (by omega))
      have hj : (i.val + 1) + (j - (i.val + 1)) = j := by have := i.isLt; omega
      rw [hj, Nat.zero_add, ← Algebra.smul_def] at hm
      have hc : (((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) =
          algebraMap ℚ (R r) (((N + 1 : ℕ) : ℚ) * ((i.val + 1 : ℕ) : ℚ) - (j : ℚ)) := by simp
      rw [mul_smul, hc]
      exact rationalCoefficient_smul_mem _ hm

theorem J_chainBasis_mem (N ell r : ℕ) (s : Finset (Fin r)) :
    CoefficientComplex.J N r ell (chainBasis r s) ∈
      chainPiece (ell - 1) r (∑ i ∈ s, (ell + i.val + 1)) s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_chainPiece (ell - 1) r
  | @insert i s hi ih =>
    obtain ⟨c, hc⟩ := chainBasis_insert_eq_unit_smul r i s hi
    rw [hc, Units.smul_def, map_zsmul]
    apply Submodule.smul_of_tower_mem
    rw [map_mul]
    change CoefficientComplex.J N r ell (CoefficientComplex.xi r i) *
      CoefficientComplex.J N r ell (chainBasis r s) ∈ _
    rw [CoefficientComplex.J_xi]
    have hm := mul_mem_chainPiece (tail_mem_chainPiece N (ell - 1) r (ell + i.val + 1)) ih
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_comm] using hm

/-- J preserves both auxiliary weight and exterior degree. -/
theorem J_mem_chainPiece {N ell r w h : ℕ} {x : A r}
    (hx : x ∈ chainPiece ell r w h) :
    CoefficientComplex.J N r ell x ∈ chainPiece (ell - 1) r w h := by
  rw [chainPiece_eq_span_degree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    change monomialDegree ell m = (w, h) at hm
    have hd := mul_mem_chainPiece (polynomialMonomial_mem (ell - 1) r m.1)
      (J_chainBasis_mem N ell r m.2)
    have hw : (∑ i : Fin r, (i.val + 1) * m.1 i) +
        (∑ i ∈ m.2, (ell + i.val + 1)) = w := congrArg Prod.fst hm
    have hh : m.2.card = h := congrArg Prod.snd hm
    rw [rationalChainBasis_apply, map_smul, Algebra.smul_def]
    rw [hw, Nat.zero_add, hh] at hd
    exact hd
  | zero => simp
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul q x hx ihx => simpa only [map_rat_smul] using Submodule.smul_mem _ q ihx

/-- Grading preservation makes J commute with homogeneous projections. -/
theorem homogeneousProjection_J (N ell r w h : ℕ) (x : A r) :
    homogeneousProjection (ell - 1) r w h (CoefficientComplex.J N r ell x) =
      CoefficientComplex.J N r ell (homogeneousProjection ell r w h x) := by
  have he : (homogeneousProjection (ell - 1) r w h).comp
      ((CoefficientComplex.J N r ell).toLinearMap.restrictScalars ℚ) =
      ((CoefficientComplex.J N r ell).toLinearMap.restrictScalars ℚ).comp
        (homogeneousProjection ell r w h) := by
    apply (rationalChainBasis r).ext
    intro m
    change homogeneousProjection (ell - 1) r w h (CoefficientComplex.J N r ell (rationalChainBasis r m)) =
      CoefficientComplex.J N r ell (homogeneousProjection ell r w h (rationalChainBasis r m))
    rw [homogeneousProjection_basis]
    have hm := J_mem_chainPiece (N := N) (rationalChainBasis_mem ell r m)
    by_cases hd : monomialDegree ell m = (w, h)
    · rw [if_pos hd]
      exact homogeneousProjection_eq_self (by simpa only [hd] using hm)
    · rw [if_neg hd, map_zero]
      exact homogeneousProjection_eq_zero_of_mem hm hd
  exact LinearMap.congr_fun he x

/-- Projecting an auxiliary cycle in any exterior degree preserves closedness. -/
theorem homogeneousProjection_cycle {N ell r : ℕ} (w h : ℕ) {x : A r}
    (hx : CoefficientComplex.d N r ell x = 0) :
    CoefficientComplex.d N r ell (homogeneousProjection ell r w h x) = 0 := by
  cases h with
  | zero => exact d_eq_zero_of_mem_chainPiece_zero (homogeneousProjection_mem _ _ _ _ _)
  | succ h => rw [← homogeneousProjection_d, hx, map_zero]

/-- Tail generation yields lifts preserving both auxiliary gradings. -/
theorem comparison_homogeneous_cycle_lift (N ell r w h : ℕ) (hN : 0 < N)
    (hell : ell ≤ N * r) {z : A r} (hz : CoefficientComplex.d N r (ell - 1) z = 0)
    (hw : z ∈ chainPiece (ell - 1) r w h) :
    ∃ v ∈ chainPiece ell r w h, CoefficientComplex.d N r ell v = 0 ∧
      ∃ u ∈ chainPiece (ell - 1) r w (h + 1),
        z = CoefficientComplex.J N r ell v + CoefficientComplex.d N r (ell - 1) u := by
  obtain ⟨v, hv, u, hu⟩ := CoefficientComplex.comparison_cycle_lift N r ell hN hell z hz
  refine ⟨homogeneousProjection ell r w h v, homogeneousProjection_mem _ _ _ _ _,
    homogeneousProjection_cycle w h hv,
    homogeneousProjection (ell - 1) r w (h + 1) u, homogeneousProjection_mem _ _ _ _ _, ?_⟩
  have he := congrArg (homogeneousProjection (ell - 1) r w h) hu
  rw [homogeneousProjection_eq_self hw, map_add, homogeneousProjection_J,
    homogeneousProjection_d] at he
  exact he

end TorusLinkHomology.HilbertSeries.Auxiliary
