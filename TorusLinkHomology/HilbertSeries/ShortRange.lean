import TorusLinkHomology.HilbertSeries.GradedDifferential
import TorusLinkHomology.Generation.MuCoordinatesGrading

/-! Linear short-range cycle coordinates, retaining the actual cycle algebra. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries
open CoordinateKoszul Generation

/-- Substitution of μ_j for ξ_j (j>0), and zero for ξ_0. -/
def cycleSubstitution (N a : ℕ) : A (a + 1) →ₐ[R (a + 1)] A (a + 1) :=
  (adaptedMuMap N a).comp (eraseAuxiliary a)

@[simp] theorem cycleSubstitution_xi_zero (N a : ℕ) :
    cycleSubstitution N a (xi (a + 1) 0) = 0 := by simp [cycleSubstitution]

@[simp] theorem cycleSubstitution_xi_succ (N a : ℕ) (i : Fin a) :
    cycleSubstitution N a (xi (a + 1) i.succ) = mu N (a + 1) (i.val + 1) := by
  simp [cycleSubstitution]

theorem cycleSubstitution_is_cycle (N a : ℕ) (x : A (a + 1)) :
    d N (a + 1) (cycleSubstitution N a x) = 0 := by
  have hm : cycleSubstitution N a x ∈ (torusLinkDGA N (a + 1)).cycles := by
    induction x using induction_on_generators (a + 1) with
    | hone => simpa only [map_one] using (torusLinkDGA N (a + 1)).cycles.one_mem
    | hadd x y hx hy => simpa only [map_add] using (torusLinkDGA N (a + 1)).cycles.add_mem hx hy
    | hsmul r x hx => simpa only [map_smul] using (torusLinkDGA N (a + 1)).cycles.smul_mem hx r
    | hxi i x hx =>
      rw [map_mul]
      apply (torusLinkDGA N (a + 1)).cycles.mul_mem _ hx
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [cycleSubstitution_xi_zero]; exact (torusLinkDGA N (a + 1)).cycles.zero_mem
      · change d N (a + 1) (cycleSubstitution N a (xi (a + 1) j.succ)) = 0
        rw [cycleSubstitution_xi_succ]
        exact mu_is_cycle N (a + 1) (j.val + 1) (by omega)
  exact hm

/-- The exterior coordinate space with the auxiliary generator erased. -/
def muCoordinateSpace (a : ℕ) : Submodule (R (a + 1)) (A (a + 1)) :=
  LinearMap.ker ((eraseAuxiliary a).toLinearMap - LinearMap.id)

@[simp] theorem mem_muCoordinateSpace (a : ℕ) (x : A (a + 1)) :
    x ∈ muCoordinateSpace a ↔ eraseAuxiliary a x = x := by
  simp [muCoordinateSpace, sub_eq_zero]

/-- The coordinate map is linear over the full polynomial ring. -/
def muCoordinateMap (N a : ℕ) :
    muCoordinateSpace a →ₗ[R (a + 1)] (torusLinkDGA N (a + 1)).cycles where
  toFun w := ⟨adaptedMuMap N a w, by
    change d N (a + 1) (adaptedMuMap N a w) = 0
    have hw := (mem_muCoordinateSpace a w).mp w.property
    have hc := cycleSubstitution_is_cycle N a w
    simpa only [cycleSubstitution, AlgHom.comp_apply, hw] using hc⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem muCoordinateMap_injective (N a : ℕ) : Function.Injective (muCoordinateMap N a) := by
  intro x y hxy
  apply Subtype.ext
  exact adaptedMuMap_injective N a (congrArg Subtype.val hxy)

theorem muCoordinateMap_surjective (N a : ℕ) (haN : a ≤ N) :
    Function.Surjective (muCoordinateMap N a) := by
  intro x
  obtain ⟨w, hw, hp⟩ := exists_mu_cycle_coordinates N a haN x x.property
  let v : A (a + 1) := (PiCoordinates.toPi (a + 1)).symm w
  have hv : v ∈ muCoordinateSpace a := by
    rw [mem_muCoordinateSpace]
    simp only [v, eraseAuxiliary, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply, hp]
  refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
  change adaptedMuMap N a v = x.val
  simp only [v, adaptedMuMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, hw, AlgEquiv.symm_apply_apply]

/-- The existing unique-coordinate theorem as a genuine linear equivalence. -/
def shortRangeCycleEquiv (N a : ℕ) (haN : a ≤ N) :
    muCoordinateSpace a ≃ₗ[R (a + 1)] (torusLinkDGA N (a + 1)).cycles :=
  LinearEquiv.ofBijective (muCoordinateMap N a)
    ⟨muCoordinateMap_injective N a, muCoordinateMap_surjective N a haN⟩

/-- Each named cycle has its expected three degrees. -/
theorem mu_mem_chainPiece (N n k : ℕ) : mu N n k ∈ chainPiece N n (N + 1) k 1 := by
  unfold mu
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  split_ifs with hij
  · have hu := u_mem_chainPiece N n i
    have hx := xi_mem_chainPiece N n j
    have hm := mul_mem_chainPiece hu hx
    have hc : ((N : R n) * (i.val : R n) - (j.val : R n)) =
        algebraMap ℚ (R n) ((N : ℚ) * (i.val : ℚ) - (j.val : ℚ)) := by simp
    rw [hc, mul_smul]
    change ((N : ℚ) * (i.val : ℚ) - (j.val : ℚ)) • (u n i • xi n j) ∈ _
    apply Submodule.smul_mem
    simpa only [Nat.add_comm 1 N, hij, zero_add, Algebra.smul_def] using hm
  · exact Submodule.zero_mem _

/-- An algebra map fixing the polynomial coefficients is graded if its exterior
images have the prescribed degrees. -/
theorem algHom_chainBasis_mem (N M n : ℕ) (f : A n →ₐ[R n] A n)
    (hf : ∀ i, f (xi n i) ∈ chainPiece M n N i.val 1) (s : Finset (Fin n)) :
    f (chainBasis n s) ∈ chainPiece M n (N * s.card) (∑ i ∈ s, i.val) s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_chainPiece M n
  | @insert i s hi ih =>
    obtain ⟨c, hc⟩ := chainBasis_insert_eq_unit_smul n i s hi
    rw [hc, Units.smul_def, map_zsmul, map_mul]
    apply Submodule.smul_of_tower_mem
    have hm := mul_mem_chainPiece (hf i) ih
    simpa only [Finset.card_insert_of_notMem hi, Finset.sum_insert hi,
      Nat.mul_add, Nat.mul_one, Nat.add_comm] using hm

theorem algHom_mem_chainPiece (N M n : ℕ) (f : A n →ₐ[R n] A n)
    (hf : ∀ i, f (xi n i) ∈ chainPiece M n N i.val 1)
    {a b h : ℕ} {x : A n} (hx : x ∈ chainPiece N n a b h) :
    f x ∈ chainPiece M n a b h := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨ha, hb, hh⟩ := m.property
    change f (rationalChainBasis n
      (Finsupp.equivFunOnFinite.symm (fun i => (m.val.1 i).val), m.val.2)) ∈ _
    rw [rationalChainBasis_apply, map_smul]
    have hm := mul_mem_chainPiece (polynomialMonomial_mem M n
      (Finsupp.equivFunOnFinite.symm (fun i => (m.val.1 i).val)))
      (algHom_chainBasis_mem N M n f hf m.val.2)
    have ha' : (∑ i : Fin n, (m.val.1 i).val) + N * h = a := by simpa only [hh] using ha
    simpa only [Finsupp.coe_equivFunOnFinite_symm, ha', hb, hh, zero_add,
      Algebra.smul_def] using hm
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using (chainPiece M n a b h).add_mem ihx ihy
  | smul r x hx ih => simpa only [map_rat_smul] using (chainPiece M n a b h).smul_mem r ih

theorem cycleSubstitution_mem_chainPiece (N n : ℕ) {a b h : ℕ} {x : A (n + 1)}
    (hx : x ∈ chainPiece (N + 1) (n + 1) a b h) :
    cycleSubstitution N n x ∈ chainPiece N (n + 1) a b h := by
  apply algHom_mem_chainPiece (N + 1) N (n + 1) (cycleSubstitution N n) _ hx
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [cycleSubstitution_xi_zero]; exact Submodule.zero_mem _
  · rw [cycleSubstitution_xi_succ]
    exact mu_mem_chainPiece N (n + 1) (j.val + 1)

/-- Graded maps commute with basis projections, including on inhomogeneous chains. -/
theorem homogeneousProjection_algHom (N M n a b h : ℕ) (f : A n →ₐ[R n] A n)
    (hf : ∀ i, f (xi n i) ∈ chainPiece M n N i.val 1) (x : A n) :
    homogeneousProjection M n a b h (f x) = f (homogeneousProjection N n a b h x) := by
  have he : (homogeneousProjection M n a b h).comp (f.toLinearMap.restrictScalars ℚ) =
      (f.toLinearMap.restrictScalars ℚ).comp (homogeneousProjection N n a b h) := by
    apply (rationalChainBasis n).ext
    intro m
    change homogeneousProjection M n a b h (f (rationalChainBasis n m)) =
      f (homogeneousProjection N n a b h (rationalChainBasis n m))
    rw [homogeneousProjection_basis]
    have hm := algHom_mem_chainPiece N M n f hf (rationalChainBasis_mem N n m)
    split_ifs with hd
    · have hd0 := congrArg Prod.fst hd
      have hd1 := congrArg (fun d => d.2.1) hd
      have hd2 := congrArg (fun d => d.2.2) hd
      rw [hd0, hd1, hd2] at hm
      exact homogeneousProjection_eq_self hm
    · rw [map_zero]
      exact homogeneousProjection_eq_zero_of_mem hm (by simpa only [Prod.eta] using hd)
  exact LinearMap.congr_fun he x

private theorem cycleSubstitution_xi_mem (N n : ℕ) (i : Fin (n + 1)) :
    cycleSubstitution N n (xi (n + 1) i) ∈ chainPiece N (n + 1) (N + 1) i.val 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [cycleSubstitution_xi_zero]; exact Submodule.zero_mem _
  · rw [cycleSubstitution_xi_succ]; exact mu_mem_chainPiece N (n + 1) (j.val + 1)

private theorem eraseAuxiliary_xi_mem (M n : ℕ) (i : Fin (n + 1)) :
    eraseAuxiliary n (xi (n + 1) i) ∈ chainPiece M (n + 1) M i.val 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [eraseAuxiliary_xi_zero]; exact Submodule.zero_mem _
  · rw [eraseAuxiliary_xi_succ]; exact xi_mem_chainPiece M (n + 1) j.succ

@[simp] theorem eraseAuxiliary_chainBasis (n : ℕ) (s : Finset (Fin (n + 1))) :
    eraseAuxiliary n (chainBasis (n + 1) s) = if 0 ∈ s then 0 else chainBasis (n + 1) s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨u, hu⟩ := chainBasis_insert_eq_unit_smul (n + 1) i s hi
    by_cases hi0 : i = 0
    · subst i
      rw [hu, Units.smul_def, map_zsmul, map_mul, eraseAuxiliary_xi_zero]
      simp
    · have hxi : eraseAuxiliary n (xi (n + 1) i) = xi (n + 1) i := by
        revert hi0
        refine Fin.cases (by simp) (fun j _ => eraseAuxiliary_xi_succ n j) i
      rw [hu, Units.smul_def, map_zsmul, map_mul, hxi, ih]
      by_cases hs : 0 ∈ s <;> simp [hs, Ne.symm hi0]

@[simp] theorem eraseAuxiliary_rationalChainBasis (n : ℕ) (m : ChainIndex (n + 1)) :
    eraseAuxiliary n (rationalChainBasis (n + 1) m) =
      if 0 ∈ m.2 then 0 else rationalChainBasis (n + 1) m := by
  classical
  rw [rationalChainBasis_apply, map_smul, eraseAuxiliary_chainBasis]
  split_ifs <;> simp

theorem repr_eraseAuxiliary (n : ℕ) (x : A (n + 1)) (m : ChainIndex (n + 1)) :
    (rationalChainBasis (n + 1)).repr (eraseAuxiliary n x) m =
      if 0 ∈ m.2 then 0 else (rationalChainBasis (n + 1)).repr x m := by
  classical
  have he : (eraseAuxiliary n).toLinearMap.restrictScalars ℚ =
      (rationalChainBasis (n + 1)).rationalDiagonal (fun m => if 0 ∈ m.2 then 0 else 1) := by
    apply (rationalChainBasis (n + 1)).ext
    intro m
    change eraseAuxiliary n (rationalChainBasis (n + 1) m) = _
    rw [eraseAuxiliary_rationalChainBasis, Module.Basis.rationalDiagonal_basis]
    split_ifs <;> simp
  change (rationalChainBasis (n + 1)).repr (((eraseAuxiliary n).toLinearMap.restrictScalars ℚ) x) m = _
  rw [he, Module.Basis.repr_rationalDiagonal]
  split_ifs <;> simp

/-- Source coordinates with polynomial/exterior grading adjusted for μ_j. -/
def muCoordinatePiece (N n a b h : ℕ) : Submodule ℚ (muCoordinateSpace n) :=
  (chainPiece (N + 1) (n + 1) a b h).comap
    ((muCoordinateSpace n).subtype.restrictScalars ℚ)

/-- The short-range coordinate map preserves all three degrees. -/
def gradedMuCoordinateMap (N n a b h : ℕ) :
    muCoordinatePiece N n a b h →ₗ[ℚ] cyclePiece N (n + 1) a b h where
  toFun w := ⟨muCoordinateMap N n w.val, by
    change adaptedMuMap N n w.val.val ∈ chainPiece N (n + 1) a b h
    have hw := (mem_muCoordinateSpace n w.val).mp w.val.property
    have hg := cycleSubstitution_mem_chainPiece N n w.property
    change cycleSubstitution N n w.val.val ∈ chainPiece N (n + 1) a b h at hg
    simpa only [cycleSubstitution, AlgHom.comp_apply, hw] using hg⟩
  map_add' _ _ := by apply Subtype.ext; exact (muCoordinateMap N n).map_add _ _
  map_smul' _ _ := by apply Subtype.ext; exact (muCoordinateMap N n).map_smul_of_tower _ _

theorem gradedMuCoordinateMap_bijective (N n a b h : ℕ) (hn : n ≤ N) :
    Function.Bijective (gradedMuCoordinateMap N n a b h) := by
  constructor
  · intro x y he
    apply Subtype.ext
    apply muCoordinateMap_injective N n
    exact congrArg Subtype.val he
  · intro x
    obtain ⟨w, hw⟩ := muCoordinateMap_surjective N n hn x.val
    let p := homogeneousProjection (N + 1) (n + 1) a b h w.val
    have hwp : p ∈ muCoordinateSpace n := by
      rw [mem_muCoordinateSpace]
      change eraseAuxiliary n (homogeneousProjection (N + 1) (n + 1) a b h w.val) = _
      rw [← homogeneousProjection_algHom (N + 1) (N + 1) (n + 1) a b h
        (eraseAuxiliary n) (eraseAuxiliary_xi_mem (N + 1) n)]
      rw [(mem_muCoordinateSpace n w).mp w.property]
    have hpg : p ∈ chainPiece (N + 1) (n + 1) a b h := homogeneousProjection_mem _ _ _ _ _ _
    refine ⟨⟨⟨p, hwp⟩, hpg⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change adaptedMuMap N n p = x.val.val
    have hfix := (mem_muCoordinateSpace n p).mp hwp
    have he : adaptedMuMap N n p = cycleSubstitution N n p := by
      simp only [cycleSubstitution, AlgHom.comp_apply, hfix]
    rw [he]
    change cycleSubstitution N n (homogeneousProjection (N + 1) (n + 1) a b h w.val) = _
    rw [← homogeneousProjection_algHom (N + 1) N (n + 1) a b h
      (cycleSubstitution N n) (cycleSubstitution_xi_mem N n)]
    have hw' : cycleSubstitution N n w.val = x.val.val := by
      simp only [cycleSubstitution, AlgHom.comp_apply, (mem_muCoordinateSpace n w).mp w.property]
      exact congrArg Subtype.val hw
    rw [hw']
    exact homogeneousProjection_eq_self x.property

/-- Graded linear coordinates for every short-range homogeneous cycle space. -/
def shortRangeGradedCycleEquiv (N n a b h : ℕ) (hn : n ≤ N) :
    muCoordinatePiece N n a b h ≃ₗ[ℚ] cyclePiece N (n + 1) a b h :=
  LinearEquiv.ofBijective (gradedMuCoordinateMap N n a b h)
    (gradedMuCoordinateMap_bijective N n a b h hn)

/-- Homogeneous source monomials with no auxiliary exterior generator. -/
def muMonomialPiece (N n a b h : ℕ) : Submodule ℚ (A (n + 1)) :=
  Submodule.span ℚ (Set.range fun m : {m : BoundedMonomial (n + 1) a //
    HasDegree (N + 1) (n + 1) a b h m ∧ 0 ∉ m.2} => chainMonomial (n + 1) a m.val)

theorem mem_muMonomialPiece (N n a b h : ℕ) (x : A (n + 1)) :
    x ∈ muMonomialPiece N n a b h ↔
      x ∈ chainPiece (N + 1) (n + 1) a b h ∧ eraseAuxiliary n x = x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      constructor
      · exact Submodule.subset_span ⟨⟨m.val, m.property.1⟩, rfl⟩
      · change eraseAuxiliary n (rationalChainBasis (n + 1) _) = _
        rw [eraseAuxiliary_rationalChainBasis, if_neg m.property.2]
        rfl
    | zero => exact ⟨Submodule.zero_mem _, map_zero _⟩
    | add x y hx hy ihx ihy => exact ⟨Submodule.add_mem _ ihx.1 ihy.1, by rw [map_add, ihx.2, ihy.2]⟩
    | smul q x hx ih => exact ⟨Submodule.smul_mem _ q ih.1, by rw [map_rat_smul, ih.2]⟩
  · rintro ⟨hx, he⟩
    rw [← he]
    clear he
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      change eraseAuxiliary n (rationalChainBasis (n + 1) _) ∈ _
      rw [eraseAuxiliary_rationalChainBasis]
      split_ifs with hm
      · exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨m.val, m.property, hm⟩, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul q x hx ih => rw [map_rat_smul]; exact Submodule.smul_mem _ q ih

def muCoordinatePieceEquivMonomials (N n a b h : ℕ) :
    muCoordinatePiece N n a b h ≃ₗ[ℚ] muMonomialPiece N n a b h where
  toFun x := ⟨x.val.val, (mem_muMonomialPiece N n a b h _).mpr
    ⟨x.property, (mem_muCoordinateSpace n x.val).mp x.val.property⟩⟩
  invFun x := ⟨⟨x.val, (mem_muCoordinateSpace n x.val).mpr
    ((mem_muMonomialPiece N n a b h _).mp x.property).2⟩,
    ((mem_muMonomialPiece N n a b h _).mp x.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Counting the polynomial monomials times squarefree μ-products in a fixed
tridegree computes the short-range cycle dimension. -/
theorem finrank_cyclePiece_shortRange (N n a b h : ℕ) (hn : n ≤ N) :
    Module.finrank ℚ (cyclePiece N (n + 1) a b h) =
      Nat.card {m : BoundedMonomial (n + 1) a //
        HasDegree (N + 1) (n + 1) a b h m ∧ 0 ∉ m.2} := by
  classical
  rw [← (shortRangeGradedCycleEquiv N n a b h hn).finrank_eq,
    (muCoordinatePieceEquivMonomials N n a b h).finrank_eq, Nat.card_eq_fintype_card]
  exact finrank_span_eq_card ((chainMonomial_linearIndependent (n + 1) a).comp
    Subtype.val Subtype.val_injective)

end TorusLinkHomology.HilbertSeries
