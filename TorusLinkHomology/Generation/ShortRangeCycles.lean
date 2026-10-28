import TorusLinkHomology.Generation.EdgeCases
import TorusLinkHomology.Generation.PiCoordinates
import DGA.ExteriorProjection

/-!
# Short-range generation on cycle representatives

This module combines adapted coordinates over the fraction field with the
two-minor denominator descent established in `ShortRange`.
-/

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.Generation

section FieldCoordinates

variable {F ι : Type*} [CommRing F] [Fintype ι] [DecidableEq ι]

/-- Erase a single coordinate before passing to the exterior algebra. -/
def eraseCoordinate (r : ι) : (ι → F) →ₗ[F] (ι → F) :=
  ExteriorAlgebra.contractionProjection (LinearMap.proj r) (Pi.single r 1)

omit [Fintype ι] in
@[simp] theorem eraseCoordinate_apply (r : ι) (v : ι → F) (i : ι) :
    eraseCoordinate r v i = if i = r then 0 else v i := by
  by_cases hi : i = r <;>
    simp [eraseCoordinate, ExteriorAlgebra.contractionProjection, hi]

theorem eraseCoordinate_basis (r i : ι) :
    eraseCoordinate (F := F) r (Pi.basisFun F ι i) =
      if i = r then 0 else Pi.basisFun F ι i := by
  ext j
  by_cases hi : i = r
  · subst i
    simp [eraseCoordinate, ExteriorAlgebra.contractionProjection]
  · simp [eraseCoordinate, ExteriorAlgebra.contractionProjection, hi, Ne.symm hi]

/-- Matrices agreeing away from the erased coordinate induce the same map
after the coordinate projection. -/
theorem matrix_comp_eraseCoordinate_eq (r : ι) (B C : Matrix ι ι F)
    (hBC : ∀ i j, j ≠ r → B i j = C i j) :
    B.toLin'.comp (eraseCoordinate r) = C.toLin'.comp (eraseCoordinate r) := by
  apply (Pi.basisFun F ι).ext
  intro j
  simp only [LinearMap.comp_apply, eraseCoordinate_basis]
  by_cases hj : j = r
  · simp [hj]
  · simp only [if_neg hj]
    ext i
    simpa [Matrix.toLin'_apply] using hBC i j hj

end FieldCoordinates

section FieldCoordinates

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- A cycle has a common adapted-coordinate representative for any two
matrices that share their kernel columns and differ only in one auxiliary
column. The resulting representative has no auxiliary exterior component. -/
theorem exists_common_cycle_coordinates (r : ι) (B C : Matrix ι ι F)
    (hB : B.det ≠ 0) (f : Module.Dual F (ι → F)) (c : F) (hc : c ≠ 0)
    (hfB : f.comp B.toLin' = c • LinearMap.proj r)
    (hBC : ∀ i j, j ≠ r → B i j = C i j)
    (x : ExteriorAlgebra F (ι → F))
    (hx : CliffordAlgebra.contractLeft (Q := 0) f x = 0) :
    ∃ w : ExteriorAlgebra F (ι → F),
      ExteriorAlgebra.map B.toLin' w = x ∧
      ExteriorAlgebra.map C.toLin' w = x ∧
      ExteriorAlgebra.map (eraseCoordinate r) w = w := by
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hleft : B⁻¹.toLin'.comp B.toLin' = LinearMap.id := by
    rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ hunit, Matrix.toLin'_one]
  have hright : B.toLin'.comp B⁻¹.toLin' = LinearMap.id := by
    rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hunit, Matrix.toLin'_one]
  have hinj := ExteriorAlgebra.map_injective ⟨B⁻¹.toLin', hleft⟩
  let w := ExteriorAlgebra.map B⁻¹.toLin' x
  have hw : ExteriorAlgebra.map B.toLin' w = x := by
    change ((ExteriorAlgebra.map B.toLin').comp (ExteriorAlgebra.map B⁻¹.toLin')) x = x
    rw [ExteriorAlgebra.map_comp_map, hright, ExteriorAlgebra.map_id]
    rfl
  have hcw : CliffordAlgebra.contractLeft (Q := 0) (c • LinearMap.proj r) w = 0 := by
    apply hinj
    rw [map_zero, ← hfB, ← ExteriorAlgebra.contractLeft_map, hw, hx]
  have hcoord : CliffordAlgebra.contractLeft (Q := 0) (LinearMap.proj r) w = 0 := by
    rw [map_smul, LinearMap.smul_apply] at hcw
    exact (smul_eq_zero.mp hcw).resolve_left hc
  have hproj : ExteriorAlgebra.map (eraseCoordinate r) w = w := by
    rw [eraseCoordinate, ExteriorAlgebra.map_contractionProjection, hcoord, mul_zero, sub_zero]
  refine ⟨w, hw, ?_, hproj⟩
  calc
    ExteriorAlgebra.map C.toLin' w =
        ExteriorAlgebra.map C.toLin' (ExteriorAlgebra.map (eraseCoordinate r) w) :=
      congrArg (ExteriorAlgebra.map C.toLin') hproj.symm
    _ = ExteriorAlgebra.map B.toLin' (ExteriorAlgebra.map (eraseCoordinate r) w) := by
      change ((ExteriorAlgebra.map C.toLin').comp (ExteriorAlgebra.map (eraseCoordinate r))) w =
        ((ExteriorAlgebra.map B.toLin').comp (ExteriorAlgebra.map (eraseCoordinate r))) w
      rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map,
        matrix_comp_eraseCoordinate_eq r B C hBC]
    _ = x := by rw [hproj, hw]

end FieldCoordinates

section IntegralCoordinates

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [LinearOrder ι]

omit [Fintype ι] in
/-- Erasing a coordinate commutes with coefficient extension. -/
theorem piBaseChange_map_eraseCoordinate (f : R →+* S) (r : ι)
    (x : ExteriorAlgebra R (ι → R)) :
    ExteriorAlgebra.piBaseChange f (ExteriorAlgebra.map (eraseCoordinate r) x) =
      ExteriorAlgebra.map (eraseCoordinate r) (ExteriorAlgebra.piBaseChange f x) := by
  have hv (v : ι → R) :
      ExteriorAlgebra.piScalarMap f (eraseCoordinate r v) =
        eraseCoordinate r (ExteriorAlgebra.piScalarMap f v) := by
    ext i
    simp only [ExteriorAlgebra.piScalarMap_apply, eraseCoordinate_apply]
    split_ifs <;> simp
  induction x using CliffordAlgebra.left_induction with
  | algebraMap q =>
    simp only [AlgHom.commutes, ExteriorAlgebra.piBaseChange,
      ExteriorAlgebra.mapOfSemilinear_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.piBaseChange_iota, hv, hx]

variable {F : Type*} [IsDomain R] [UniqueFactorizationMonoid R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- Common adapted coordinates of an integral cycle descend to the original
ring whenever the two adapted determinants are relatively prime. -/
theorem exists_integral_cycle_coordinates (r : ι) (B C : Matrix ι ι R)
    (hBCdet : IsRelPrime B.det C.det) (hB : B.det ≠ 0)
    (f : Module.Dual F (ι → F)) (c : F) (hc : c ≠ 0)
    (hfB : f.comp (B.map (algebraMap R F)).toLin' = c • LinearMap.proj r)
    (hBC : ∀ i j, j ≠ r → B i j = C i j)
    (x : ExteriorAlgebra R (ι → R))
    (hx : CliffordAlgebra.contractLeft (Q := 0) f
      (ExteriorAlgebra.piBaseChange (algebraMap R F) x) = 0) :
    ∃ w : ExteriorAlgebra R (ι → R),
      ExteriorAlgebra.map B.toLin' w = x ∧
      ExteriorAlgebra.map (eraseCoordinate r) w = w := by
  have hinj := ExteriorAlgebra.piBaseChange_injective (ι := ι) (algebraMap R F)
    (IsFractionRing.injective R F)
  have hB' : (B.map (algebraMap R F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hB ((IsFractionRing.injective R F) (by simpa using h))
  obtain ⟨w, hwB, hwC, hwP⟩ := exists_common_cycle_coordinates r
    (B.map (algebraMap R F)) (C.map (algebraMap R F)) hB' f c hc hfB
    (fun i j hj => congrArg (algebraMap R F) (hBC i j hj)) _ hx
  have hw : ∀ s, IsLocalization.IsInteger R ((Pi.basisFun F ι).ExteriorAlgebra.repr w s) := by
    apply isInteger_exteriorAlgebra_coordinate_of_isRelPrime_dets B C hBCdet w
    · intro s
      rw [hwB, ExteriorAlgebra.repr_piBaseChange]
      exact ⟨_, rfl⟩
    · intro s
      rw [hwC, ExteriorAlgebra.repr_piBaseChange]
      exact ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := (ExteriorAlgebra.exists_piBaseChange_eq_iff (algebraMap R F) w).mpr hw
  refine ⟨v, ?_, ?_⟩
  · apply hinj
    rw [ExteriorAlgebra.piBaseChange_map_matrix, hv, hwB]
  · apply hinj
    rw [piBaseChange_map_eraseCoordinate, hv, hwP]

omit [UniqueFactorizationMonoid R] in
/-- A matrix with nonzero determinant induces an injective map on the full
exterior algebra over a domain. This is proved after passing to its fraction
field, where the matrix has an inverse. -/
theorem exteriorAlgebra_matrix_map_injective (B : Matrix ι ι R) (hB : B.det ≠ 0) :
    Function.Injective (ExteriorAlgebra.map B.toLin') := by
  let F := FractionRing R
  have hB' : (B.map (algebraMap R F)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hB ((IsFractionRing.injective R F) (by simpa using h))
  have hunit : IsUnit (B.map (algebraMap R F)).det := isUnit_iff_ne_zero.mpr hB'
  have hinj := ExteriorAlgebra.map_injective
    (f := (B.map (algebraMap R F)).toLin') ⟨(B.map (algebraMap R F))⁻¹.toLin', by
      rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ hunit, Matrix.toLin'_one]⟩
  intro x y hxy
  apply ExteriorAlgebra.piBaseChange_injective (algebraMap R F) (IsFractionRing.injective R F)
  apply hinj
  rw [← ExteriorAlgebra.piBaseChange_map_matrix,
    ← ExteriorAlgebra.piBaseChange_map_matrix, hxy]

end IntegralCoordinates

section ConcreteFunctional

/-- The differential functional after extension of the coefficient ring. -/
def extendedFunctional (N n : ℕ) {S : Type*} [CommRing S] [Algebra (R n) S] :
    Module.Dual S (Fin n → S) :=
  ∑ i : Fin n, algebraMap (R n) S (differentialCoefficient N n i) • LinearMap.proj i

theorem extendedFunctional_apply (N n : ℕ) {S : Type*} [CommRing S] [Algebra (R n) S]
    (v : Fin n → S) : extendedFunctional N n v =
      ∑ i : Fin n, algebraMap (R n) S (differentialCoefficient N n i) * v i := by
  simp [extendedFunctional, Algebra.smul_def]

@[simp] theorem extendedFunctional_basis (N n : ℕ) {S : Type*}
    [CommRing S] [Algebra (R n) S] (i : Fin n) :
    extendedFunctional N n (Pi.basisFun S (Fin n) i) =
      algebraMap (R n) S (differentialCoefficient N n i) := by
  simp [extendedFunctional_apply, Pi.basisFun_apply, Pi.single_apply]

theorem extendedFunctional_scalarMap (N n : ℕ) {S : Type*}
    [CommRing S] [Algebra (R n) S] (v : Fin n → R n) :
    extendedFunctional N n (ExteriorAlgebra.piScalarMap (algebraMap (R n) S) v) =
      algebraMap (R n) S (PiCoordinates.functional N n v) := by
  simp [extendedFunctional_apply, PiCoordinates.functional_apply, map_sum]

/-- The named cycle columns are in the degree-one kernel over the original ring. -/
theorem functional_muMatrix (N a : ℕ) (j : Fin a) :
    PiCoordinates.functional N (a + 1) (fun i => muMatrix N a i j) = 0 := by
  have h := congrArg (PiCoordinates.toPi (a + 1))
    (mu_is_cycle N (a + 1) (j.val + 1) (by omega))
  rw [PiCoordinates.toPi_d, PiCoordinates.toPi_mu, map_zero] at h
  change CliffordAlgebra.contractLeft (Q := 0) (PiCoordinates.functional N (a + 1))
    (ExteriorAlgebra.ι (R (a + 1)) (fun i => muMatrix N a i j)) = 0 at h
  rw [CliffordAlgebra.contractLeft_ι] at h
  exact (ExteriorAlgebra.algebraMap_eq_zero_iff _ _).mp h

@[simp] theorem differentialCoefficient_zero (N a : ℕ) :
    differentialCoefficient N (a + 1) 0 = u (a + 1) 0 ^ N := by
  change Polynomial.constantCoeff ((uPolynomial (a + 1)) ^ N) = _
  rw [map_pow]
  congr 1
  change (uPolynomial (a + 1)).coeff 0 = _
  simp only [uPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    exact if_neg (fun h => hj (Fin.ext h))
  · simp

/-- In the first adapted basis the functional is a nonzero multiple of the
auxiliary coordinate and vanishes on all cycle columns. -/
theorem extendedFunctional_comp_muAdjoinedMatrix (N a : ℕ) {S : Type*}
    [CommRing S] [Algebra (R (a + 1)) S] :
    (extendedFunctional N (a + 1)).comp
      ((muAdjoinedMatrix N a 0).map (algebraMap (R (a + 1)) S)).toLin' =
      algebraMap (R (a + 1)) S (u (a + 1) 0 ^ N) • LinearMap.proj 0 := by
  apply (Pi.basisFun S (Fin (a + 1))).ext
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · have hzero : ((muAdjoinedMatrix N a 0).map (algebraMap (R (a + 1)) S)).toLin'
        (Pi.basisFun S (Fin (a + 1)) 0) = Pi.basisFun S (Fin (a + 1)) 0 := by
      ext i
      simp [Matrix.toLin'_apply, muAdjoinedMatrix, Pi.basisFun_apply, Pi.single_apply]
    rw [LinearMap.comp_apply, hzero, extendedFunctional_basis, differentialCoefficient_zero]
    simp
  · have hcol : ((muAdjoinedMatrix N a 0).map (algebraMap (R (a + 1)) S)).toLin'
        (Pi.basisFun S (Fin (a + 1)) j.succ) =
        ExteriorAlgebra.piScalarMap (algebraMap (R (a + 1)) S)
          (fun i => muMatrix N a i j) := by
      ext i
      simp [Matrix.toLin'_apply]
    rw [LinearMap.comp_apply, hcol, extendedFunctional_scalarMap, functional_muMatrix, map_zero]
    simp [Pi.basisFun_apply]

end ConcreteFunctional

/-- Substitute the named cycles for the successor coordinates and zero for
the auxiliary coordinate, in the original exterior algebra. -/
def piMuMap (N a : ℕ) : PiCoordinates.PiA (a + 1) →ₐ[R (a + 1)] A (a + 1) :=
  (PiCoordinates.toPi (a + 1)).symm.toAlgHom.comp
    ((ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin').comp
      (ExteriorAlgebra.map (eraseCoordinate 0)))

@[simp] theorem piMuMap_iota_zero (N a : ℕ) :
    piMuMap N a (ExteriorAlgebra.ι (R (a + 1))
      (Pi.basisFun (R (a + 1)) (Fin (a + 1)) 0)) = 0 := by
  simp only [piMuMap, AlgHom.comp_apply,
    ExteriorAlgebra.map_apply_ι, eraseCoordinate_basis, ↓reduceIte, map_zero]

@[simp] theorem piMuMap_iota_succ (N a : ℕ) (j : Fin a) :
    piMuMap N a (ExteriorAlgebra.ι (R (a + 1))
      (Pi.basisFun (R (a + 1)) (Fin (a + 1)) j.succ)) =
      mu N (a + 1) (j.val + 1) := by
  have hcol : (muAdjoinedMatrix N a 0).toLin'
      (Pi.basisFun (R (a + 1)) (Fin (a + 1)) j.succ) =
      (fun i => muMatrix N a i j) := by
    ext i
    simp [Matrix.toLin'_apply]
  simp only [piMuMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    ExteriorAlgebra.map_apply_ι, eraseCoordinate_basis, Fin.succ_ne_zero, ↓reduceIte,
    hcol]
  rw [← PiCoordinates.toPi_mu, AlgEquiv.symm_apply_apply]

/-- Every value of the cycle substitution map belongs to the named-cycle
subalgebra over the coefficient ring. -/
theorem piMuMap_mem (N a : ℕ) (x : PiCoordinates.PiA (a + 1)) :
    piMuMap N a x ∈ muSubalgebra N (a + 1) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact (muSubalgebra N (a + 1)).algebraMap_mem r
  | ι m =>
    rw [← (Pi.basisFun (R (a + 1)) (Fin (a + 1))).sum_repr m]
    simp only [map_sum, map_smul]
    apply Subalgebra.sum_mem
    intro j _
    apply Subalgebra.smul_mem
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [piMuMap_iota_zero]
      exact Subalgebra.zero_mem _
    · rw [piMuMap_iota_succ]
      apply Algebra.subset_adjoin
      exact ⟨j.val + 1, by omega, by omega, rfl⟩
  | mul x y hx hy => simpa only [map_mul] using (muSubalgebra N (a + 1)).mul_mem hx hy
  | add x y hx hy => simpa only [map_add] using (muSubalgebra N (a + 1)).add_mem hx hy

/-- Every short-range cycle has integral coordinates in the first adapted
matrix, and these coordinates are fixed by erasing the auxiliary generator. -/
theorem exists_mu_cycle_coordinates (N a : ℕ) (haN : a ≤ N)
    (x : A (a + 1)) (hx : d N (a + 1) x = 0) :
    ∃ w : PiCoordinates.PiA (a + 1),
      ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin' w = PiCoordinates.toPi (a + 1) x ∧
      ExteriorAlgebra.map (eraseCoordinate 0) w = w := by
  let F := FractionRing (R (a + 1))
  let f : Module.Dual F (Fin (a + 1) → F) := extendedFunctional N (a + 1)
  let c : F := algebraMap (R (a + 1)) F (u (a + 1) 0 ^ N)
  have hc : c ≠ 0 := by
    intro h
    have hu : u (a + 1) 0 ^ N = 0 :=
      (IsFractionRing.injective (R (a + 1)) F) (by simpa [c] using h)
    exact pow_ne_zero N (MvPolynomial.X_ne_zero _) hu
  have hcycle : CliffordAlgebra.contractLeft (Q := 0) f
      (ExteriorAlgebra.piBaseChange (algebraMap (R (a + 1)) F)
        (PiCoordinates.toPi (a + 1) x)) = 0 := by
    rw [ExteriorAlgebra.piBaseChange, ExteriorAlgebra.contractLeft_mapOfSemilinear
      _ _ (PiCoordinates.functional N (a + 1)) f
        (extendedFunctional_scalarMap N (a + 1))]
    change ExteriorAlgebra.piBaseChange (algebraMap (R (a + 1)) F)
      (PiCoordinates.piDifferential N (a + 1) (PiCoordinates.toPi (a + 1) x)) = 0
    rw [← PiCoordinates.toPi_d, hx, map_zero, map_zero]
  have hcols : ∀ i j : Fin (a + 1), j ≠ 0 →
      muAdjoinedMatrix N a 0 i j = muAdjoinedMatrix N a (Fin.last a) i j := by
    intro i j hj
    refine Fin.cases (fun h => False.elim (h rfl)) (fun j _ => ?_) j hj
    rfl
  exact exists_integral_cycle_coordinates (F := F) 0
    (muAdjoinedMatrix N a 0) (muAdjoinedMatrix N a (Fin.last a))
    (muAdjoinedMatrices_isRelPrime N a haN)
    (by simpa using muFirstMinor_det_ne_zero N a) f c hc
    (extendedFunctional_comp_muAdjoinedMatrix N a) hcols
    (PiCoordinates.toPi (a + 1) x) hcycle

/-- The first adapted exterior map is injective even before restricting to
the short range. -/
theorem muAdjoinedMatrix_zero_map_injective (N a : ℕ) :
    Function.Injective (ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin') :=
  exteriorAlgebra_matrix_map_injective
    (muAdjoinedMatrix N a 0) (by simpa using muFirstMinor_det_ne_zero N a)

/-- Canonical integral exterior coordinates of a short-range cycle. These
coordinates are unique and contain no auxiliary exterior generator. -/
theorem existsUnique_mu_cycle_coordinates (N a : ℕ) (haN : a ≤ N)
    (x : A (a + 1)) (hx : d N (a + 1) x = 0) :
    ∃! w : PiCoordinates.PiA (a + 1),
      ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin' w = PiCoordinates.toPi (a + 1) x ∧
      ExteriorAlgebra.map (eraseCoordinate 0) w = w := by
  obtain ⟨w, hw, hp⟩ := exists_mu_cycle_coordinates N a haN x hx
  refine ⟨w, ⟨hw, hp⟩, ?_⟩
  intro v hv
  exact muAdjoinedMatrix_zero_map_injective N a (hv.1.trans hw.symm)

/-- In the short range, every cycle is itself a polynomial in the named cycles.
No boundary correction is needed. -/
theorem shortRange_cycle_mem (N a : ℕ) (haN : a ≤ N)
    (x : A (a + 1)) (hx : d N (a + 1) x = 0) :
    x ∈ muSubalgebra N (a + 1) := by
  obtain ⟨w, hw, hp⟩ := exists_mu_cycle_coordinates N a haN x hx
  have hvalue : piMuMap N a w = x := by
    change (PiCoordinates.toPi (a + 1)).symm
      (ExteriorAlgebra.map (muAdjoinedMatrix N a 0).toLin'
        (ExteriorAlgebra.map (eraseCoordinate 0) w)) = x
    rw [hp, hw, AlgEquiv.symm_apply_apply]
  rw [← hvalue]
  exact piMuMap_mem N a w

/-- Short-range generation, in the representative-level statement used by
the main induction. -/
theorem shortRange_cycleGeneration (N a : ℕ) (haN : a ≤ N) :
    (∀ k : ℕ, 1 ≤ k → k < a + 1 → d N (a + 1) (mu N (a + 1) k) = 0) ∧
    (∀ x : A (a + 1), d N (a + 1) x = 0 →
      ∃ p : A (a + 1), p ∈ muSubalgebra N (a + 1) ∧
        ∃ b : A (a + 1), x = p + d N (a + 1) b) := by
  constructor
  · intro k _ hk
    exact mu_is_cycle N (a + 1) k hk
  · intro x hx
    exact ⟨x, shortRange_cycle_mem N a haN x hx, 0, by simp⟩

/-- Short-range generation at every length `n ≤ N + 1`, including the empty
complex. The positive-length argument also covers exponent zero. -/
theorem shortRange (N n : ℕ) (hn : n ≤ N + 1) :
    (∀ k : ℕ, 1 ≤ k → k < n → d N n (mu N n k) = 0) ∧
    (∀ a : A n, d N n a = 0 →
      ∃ p : A n, p ∈ muSubalgebra N n ∧ ∃ b : A n, a = p + d N n b) := by
  cases n with
  | zero => exact zero_variables N
  | succ a => exact shortRange_cycleGeneration N a (by omega)

end TorusLinkHomology.Generation
