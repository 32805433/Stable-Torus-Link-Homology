import TorusLinkHomology.HilbertSeries.AuxiliaryGrading

/-! Grading of the common inclusion and the shifted comparison projection. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries.Auxiliary
open CoordinateKoszul

private theorem pow_mem {ell r w h : ℕ} {x : A r}
    (hx : x ∈ chainPiece ell r w h) (k : ℕ) :
    x ^ k ∈ chainPiece ell r (w * k) (h * k) := by
  induction k with
  | zero => simpa using one_mem_chainPiece ell r
  | succ k ih => simpa only [pow_succ, Nat.mul_succ] using mul_mem_chainPiece ih hx

private theorem polynomialMap_monomial_mem (ell r s : ℕ) (f : R r →+* R s)
    (hf : ∀ i, algebraMap (R s) (A s) (f (CoefficientComplex.e r i)) ∈ chainPiece ell s (i.val + 1) 0)
    (m : Fin r →₀ ℕ) :
    algebraMap (R s) (A s) (f (MvPolynomial.monomial m (1 : ℚ))) ∈
      chainPiece ell s (∑ i : Fin r, (i.val + 1) * m i) 0 := by
  classical
  have hm : (MvPolynomial.monomial m (1 : ℚ) : R r) = ∏ i : Fin r, CoefficientComplex.e r i ^ m i := by
    rw [← MvPolynomial.prod_X_pow_eq_monomial]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i hi hn
    simp [Finsupp.notMem_support_iff.mp hn]
  rw [hm]
  suffices hp : ∀ t : Finset (Fin r),
      algebraMap (R s) (A s) (f (∏ i ∈ t, CoefficientComplex.e r i ^ m i)) ∈
        chainPiece ell s (∑ i ∈ t, (i.val + 1) * m i) 0 from hp Finset.univ
  intro t
  induction t using Finset.induction_on with
  | empty => simpa using one_mem_chainPiece ell s
  | @insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, map_mul, map_mul, map_pow, map_pow]
    have hp := pow_mem (hf i) (m i)
    simpa only [zero_mul, zero_add] using mul_mem_chainPiece hp ih

/-- A semilinear exterior map is homogeneous if its coefficient and exterior
images have the required weights. -/
private theorem ringHom_mem_chainPiece (ell ell' r s : ℕ) (f : A r →+* A s)
    (c : R r →+* R s)
    (hc : ∀ q, f (algebraMap (R r) (A r) q) = algebraMap (R s) (A s) (c q))
    (he : ∀ i, algebraMap (R s) (A s) (c (CoefficientComplex.e r i)) ∈ chainPiece ell' s (i.val + 1) 0)
    (hx : ∀ i, f (xi r i) ∈ chainPiece ell' s (ell + i.val + 1) 1)
    {w h : ℕ} {x : A r} (hg : x ∈ chainPiece ell r w h) :
    f x ∈ chainPiece ell' s w h := by
  have hb (t : Finset (Fin r)) : f (chainBasis r t) ∈
      chainPiece ell' s (∑ i ∈ t, (ell + i.val + 1)) t.card := by
    classical
    induction t using Finset.induction_on with
    | empty => simpa using one_mem_chainPiece ell' s
    | @insert i t hi ih =>
      obtain ⟨u, hu⟩ := chainBasis_insert_eq_unit_smul r i t hi
      rw [hu, Units.smul_def, map_zsmul, map_mul]
      apply Submodule.smul_of_tower_mem
      simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_comm 1] using
        mul_mem_chainPiece (hx i) ih
  induction hg using Submodule.span_induction with
  | mem x hxg =>
    obtain ⟨m, rfl⟩ := hxg
    obtain ⟨hw, hh⟩ := m.property
    change f (rationalChainBasis r
      (Finsupp.equivFunOnFinite.symm (fun i => (m.val.1 i).val), m.val.2)) ∈ _
    rw [rationalChainBasis_apply, Algebra.smul_def, map_mul, hc]
    have hp := polynomialMap_monomial_mem ell' r s c he
      (Finsupp.equivFunOnFinite.symm (fun i => (m.val.1 i).val))
    simpa only [Finsupp.coe_equivFunOnFinite_symm, hw, hh, zero_add] using
      mul_mem_chainPiece hp (hb m.val.2)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using (chainPiece ell' s w h).add_mem ihx ihy
  | smul q x hx ih => simpa only [map_rat_smul] using (chainPiece ell' s w h).smul_mem q ih

theorem includeCommon_mem_chainPiece {ell r w h : ℕ} {x : A r}
    (hx : x ∈ chainPiece (ell + 1) r w h) :
    CoefficientComplex.includeCommon r x ∈ chainPiece ell (r + 1) w h := by
  apply ringHom_mem_chainPiece (ell + 1) ell r (r + 1) (CoefficientComplex.includeCommon r)
    (CoefficientComplex.includeCoefficients r).toRingHom
    (CoefficientComplex.includeCommon_algebraMap r) _ _ hx
  · intro i
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, CoefficientComplex.includeCoefficients_e,
      Fin.val_castSucc] using e_mem_chainPiece ell (r + 1) i.castSucc
  · intro i
    change CoefficientComplex.includeCommon r (CoefficientComplex.xi r i) ∈ _
    rw [CoefficientComplex.includeCommon_xi]
    simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      xi_mem_chainPiece ell (r + 1) i.succ

theorem dropFirst_mem_chainPiece {ell r w h : ℕ} {x : A (r + 1)}
    (hx : x ∈ chainPiece ell (r + 1) w h) :
    CoefficientComplex.dropFirst r x ∈ chainPiece (ell + 1) r w h := by
  apply ringHom_mem_chainPiece ell (ell + 1) (r + 1) r (CoefficientComplex.dropFirst r)
    (CoefficientComplex.reduceCoefficients r).toRingHom
    (CoefficientComplex.dropFirst_algebraMap r) _ _ hx
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        CoefficientComplex.reduceCoefficients_e_last, map_zero]
      exact Submodule.zero_mem _
    · simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        CoefficientComplex.reduceCoefficients_e_castSucc, Fin.val_castSucc] using
        e_mem_chainPiece (ell + 1) r j
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change CoefficientComplex.dropFirst r (CoefficientComplex.xi (r + 1) 0) ∈ _
      rw [CoefficientComplex.dropFirst_xi_zero]; exact Submodule.zero_mem _
    · change CoefficientComplex.dropFirst r (CoefficientComplex.xi (r + 1) j.succ) ∈ _
      rw [CoefficientComplex.dropFirst_xi_succ]
      simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        xi_mem_chainPiece (ell + 1) r j

private theorem firstContraction_chainBasis_zero (r : ℕ) (s : Finset (Fin (r + 1)))
    (hs : 0 ∉ s) : CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm (R (r + 1)) (V (r + 1))))
      (CoefficientComplex.firstCoordinate r) (chainBasis (r + 1) s) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hi0 : i ≠ 0 := by intro he; subst i; exact hs (Finset.mem_insert_self _ _)
    have hs0 : 0 ∉ s := by intro h; exact hs (Finset.mem_insert_of_mem h)
    obtain ⟨u, hu⟩ := chainBasis_insert_eq_unit_smul (r + 1) i s hi
    rw [hu, Units.smul_def, map_zsmul, contractLeft_xi_mul, ih hs0]
    simp [CoefficientComplex.firstCoordinate, hi0]

private theorem p_chainBasis_of_mem (r : ℕ) (s : Finset (Fin (r + 1))) (hs : 0 ∈ s) :
    ∃ u : ℤˣ, CoefficientComplex.p r (chainBasis (r + 1) s) =
      u • CoefficientComplex.dropFirst r (chainBasis (r + 1) (s.erase 0)) := by
  classical
  obtain ⟨u, hu⟩ := chainBasis_insert_eq_unit_smul (r + 1) 0 (s.erase 0) (Finset.notMem_erase _ _)
  rw [Finset.insert_erase hs] at hu
  refine ⟨u, ?_⟩
  unfold CoefficientComplex.p
  rw [hu, Units.smul_def, map_zsmul, map_zsmul, contractLeft_xi_mul,
    firstContraction_chainBasis_zero r (s.erase 0) (Finset.notMem_erase _ _)]
  simp [CoefficientComplex.firstCoordinate, Units.smul_def]

private theorem reduce_monomial_mem (ell r : ℕ) (m : Fin (r + 1) →₀ ℕ) :
    algebraMap (R r) (A r) (CoefficientComplex.reduceCoefficients r (MvPolynomial.monomial m (1 : ℚ))) ∈
      chainPiece (ell + 1) r (∑ i : Fin (r + 1), (i.val + 1) * m i) 0 := by
  apply polynomialMap_monomial_mem (ell + 1) (r + 1) r
    (CoefficientComplex.reduceCoefficients r).toRingHom _ m
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      CoefficientComplex.reduceCoefficients_e_last, map_zero]
    exact Submodule.zero_mem _
  · simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      CoefficientComplex.reduceCoefficients_e_castSucc, Fin.val_castSucc] using
      e_mem_chainPiece (ell + 1) r j

/-- Projection removes the first odd generator of weight ell+1. -/
theorem p_mem_chainPiece {ell r w h : ℕ} {x : A (r + 1)}
    (hx : x ∈ chainPiece ell (r + 1) (w + (ell + 1)) (h + 1)) :
    CoefficientComplex.p r x ∈ chainPiece (ell + 1) r w h := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨hw, hh⟩ := m.property
    change CoefficientComplex.p r (rationalChainBasis (r + 1)
      (Finsupp.equivFunOnFinite.symm (fun i => (m.val.1 i).val), m.val.2)) ∈ _
    rw [rationalChainBasis_apply, CoefficientComplex.p_smul]
    by_cases hs : 0 ∈ m.val.2
    · obtain ⟨u, hu⟩ := p_chainBasis_of_mem r m.val.2 hs
      rw [hu, Units.smul_def, smul_comm]
      apply Submodule.smul_of_tower_mem
      have hp := reduce_monomial_mem ell r (Finsupp.equivFunOnFinite.symm (fun i => (m.val.1 i).val))
      have he := dropFirst_mem_chainPiece (chainBasis_mem_chainPiece ell (r + 1) (m.val.2.erase 0))
      have hcard : (m.val.2.erase 0).card = h := by rw [Finset.card_erase_of_mem hs, hh]; omega
      have hsum : (∑ i ∈ m.val.2, (ell + i.val + 1)) =
          (ell + 1) + ∑ i ∈ m.val.2.erase 0, (ell + i.val + 1) := by
        rw [← Finset.add_sum_erase _ _ hs]; simp
      have hweight : (∑ i : Fin (r + 1), (i.val + 1) * (m.val.1 i).val) +
          (∑ i ∈ m.val.2.erase 0, (ell + i.val + 1)) = w := by omega
      simpa only [Algebra.smul_def, Finsupp.coe_equivFunOnFinite_symm,
        hcard, hweight, zero_add] using mul_mem_chainPiece hp he
    · have hz : CoefficientComplex.p r (chainBasis (r + 1) m.val.2) = 0 := by
        unfold CoefficientComplex.p
        rw [firstContraction_chainBasis_zero r m.val.2 hs, map_zero]
      rw [hz, smul_zero]; exact Submodule.zero_mem _
  | zero => simp [CoefficientComplex.p]
  | add x y hx hy ihx ihy => rw [CoefficientComplex.p_add]; exact Submodule.add_mem _ ihx ihy
  | smul q x hx ih =>
    have he : CoefficientComplex.p r (q • x) = q • CoefficientComplex.p r x := by
      simp only [CoefficientComplex.p, map_rat_smul]
    rw [he]; exact Submodule.smul_mem _ q ih

/-- No first odd generator can occur below its weight, or in exterior degree zero. -/
theorem p_eq_zero_of_low_degree {ell r w h : ℕ} {x : A (r + 1)}
    (hx : x ∈ chainPiece ell (r + 1) w h) (hlow : w < ell + 1 ∨ h = 0) :
    CoefficientComplex.p r x = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨hw, hh⟩ := m.property
    have hs : 0 ∉ m.val.2 := by
      intro hs
      rcases hlow with hlow | hlow
      · have he := Finset.single_le_sum
          (fun i (_ : i ∈ m.val.2) => Nat.zero_le (ell + i.val + 1)) hs
        simp only [Fin.val_zero, add_zero] at he
        omega
      · have he : m.val.2 = ∅ := Finset.card_eq_zero.mp (hh.trans hlow)
        simp only [he, Finset.notMem_empty] at hs
    change CoefficientComplex.p r (rationalChainBasis (r + 1)
      (Finsupp.equivFunOnFinite.symm (fun i => (m.val.1 i).val), m.val.2)) = 0
    rw [rationalChainBasis_apply, CoefficientComplex.p_smul]
    unfold CoefficientComplex.p
    rw [firstContraction_chainBasis_zero r m.val.2 hs, map_zero, smul_zero]
  | zero => simp [CoefficientComplex.p]
  | add x y hx hy ihx ihy => rw [CoefficientComplex.p_add, ihx, ihy, add_zero]
  | smul q x hx ih =>
    have he : CoefficientComplex.p r (q • x) = q • CoefficientComplex.p r x := by
      simp only [CoefficientComplex.p, map_rat_smul]
    rw [he, ih, smul_zero]

/-- Projection onto a quotient degree comes from projection onto its shifted
middle degree. This also covers middle degrees below the shift. -/
theorem homogeneousProjection_p (ell r w h : ℕ) (x : A (r + 1)) :
    homogeneousProjection (ell + 1) r w h (CoefficientComplex.p r x) =
      CoefficientComplex.p r (homogeneousProjection ell (r + 1) (w + (ell + 1)) (h + 1) x) := by
  let pm : A (r + 1) →ₗ[ℚ] A r :=
    { toFun := CoefficientComplex.p r
      map_add' := CoefficientComplex.p_add r
      map_smul' q x := by simp only [CoefficientComplex.p, map_rat_smul, RingHom.id_apply] }
  have he : (homogeneousProjection (ell + 1) r w h).comp pm =
      pm.comp (homogeneousProjection ell (r + 1) (w + (ell + 1)) (h + 1)) := by
    apply (rationalChainBasis (r + 1)).ext
    intro m
    change homogeneousProjection (ell + 1) r w h (CoefficientComplex.p r (rationalChainBasis (r + 1) m)) =
      CoefficientComplex.p r (homogeneousProjection ell (r + 1) (w + (ell + 1)) (h + 1)
        (rationalChainBasis (r + 1) m))
    rw [homogeneousProjection_basis]
    have hm := rationalChainBasis_mem ell (r + 1) m
    by_cases hlow : (monomialDegree ell m).1 < ell + 1 ∨ (monomialDegree ell m).2 = 0
    · have hp := p_eq_zero_of_low_degree hm hlow
      rw [hp, map_zero]
      split_ifs with hd
      · exact hp.symm
      · simp [CoefficientComplex.p]
    · push Not at hlow
      have hw : (monomialDegree ell m).1 - (ell + 1) + (ell + 1) = (monomialDegree ell m).1 :=
        Nat.sub_add_cancel hlow.1
      have hh : (monomialDegree ell m).2 - 1 + 1 = (monomialDegree ell m).2 := by omega
      have hp : CoefficientComplex.p r (rationalChainBasis (r + 1) m) ∈
          chainPiece (ell + 1) r ((monomialDegree ell m).1 - (ell + 1)) ((monomialDegree ell m).2 - 1) :=
        p_mem_chainPiece (by simpa only [hw, hh] using hm)
      split_ifs with hd
      · have hd0 := congrArg Prod.fst hd
        have hd1 := congrArg Prod.snd hd
        rw [hd0, hd1, Nat.add_sub_cancel, Nat.add_sub_cancel] at hp
        exact homogeneousProjection_eq_self hp
      · have hn : ((monomialDegree ell m).1 - (ell + 1), (monomialDegree ell m).2 - 1) ≠ (w, h) := by
          intro he
          apply hd
          apply Prod.ext
          · have := congrArg Prod.fst he; dsimp at this; omega
          · have := congrArg Prod.snd he; dsimp at this; omega
        rw [homogeneousProjection_eq_zero_of_mem hp hn]
        simp [CoefficientComplex.p]
  exact LinearMap.congr_fun he x

end TorusLinkHomology.HilbertSeries.Auxiliary
