import TorusLinkHomology.Generation.CoefficientReduction
import DGA.ExteriorProjection
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Exactness of the coefficient-complex comparison

Contraction isolates the part of an exterior chain containing a distinguished
generator. Replacing that generator while fixing its complement gives the
injectivity and image calculation for the comparison short exact sequence.
-/

noncomputable section

namespace ExteriorAlgebra

variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

theorem contractLeft_projection (f : Module.Dual S M) (v : M) (hv : f v = 1)
    (x : ExteriorAlgebra S M) :
    CliffordAlgebra.contractLeft (Q := 0) f (map (contractionProjection f v) x) = 0 := by
  rw [map_contractionProjection, map_sub, CliffordAlgebra.contractLeft_ι_mul,
    hv, one_smul, CliffordAlgebra.contractLeft_contractLeft, mul_zero, sub_zero, sub_self]

/-- Replace the distinguished vector by `a`, fixing the kernel of `f`. -/
def replaceCoordinate (f : Module.Dual S M) (v a : M) : M →ₗ[S] M :=
  contractionProjection f (v - a)

theorem map_replaceCoordinate (f : Module.Dual S M) (v a : M)
    (x : ExteriorAlgebra S M) :
    map (replaceCoordinate f v a) x =
      x - ι S (v - a) * CliffordAlgebra.contractLeft (Q := 0) f x :=
  map_contractionProjection f (v - a) x

theorem contractLeft_replaceCoordinate (f : Module.Dual S M) (v a : M)
    (hv : f v = 1) (x : ExteriorAlgebra S M) :
    CliffordAlgebra.contractLeft (Q := 0) f (map (replaceCoordinate f v a) x) =
      f a • CliffordAlgebra.contractLeft (Q := 0) f x := by
  rw [map_replaceCoordinate, map_sub, CliffordAlgebra.contractLeft_ι_mul,
    map_sub, hv, CliffordAlgebra.contractLeft_contractLeft, mul_zero, sub_zero]
  simp only [sub_smul, one_smul, sub_sub_cancel]

theorem map_replaceCoordinate_injective (f : Module.Dual S M) (v a : M)
    (hv : f v = 1)
    (ha : Function.Injective (fun x : ExteriorAlgebra S M => f a • x)) :
    Function.Injective (map (replaceCoordinate f v a)) := by
  intro x y hxy
  have hd := congrArg (CliffordAlgebra.contractLeft (Q := 0) f) hxy
  rw [contractLeft_replaceCoordinate f v a hv,
    contractLeft_replaceCoordinate f v a hv] at hd
  have hd' := ha hd
  rw [map_replaceCoordinate, map_replaceCoordinate, hd'] at hxy
  exact sub_left_injective hxy

theorem mem_range_map_replaceCoordinate_iff (f : Module.Dual S M) (v a : M)
    (hv : f v = 1)
    (ha : Function.Injective (fun x : ExteriorAlgebra S M => f a • x))
    (x : ExteriorAlgebra S M) :
    (∃ y, map (replaceCoordinate f v a) y = x) ↔
      ∃ b, CliffordAlgebra.contractLeft (Q := 0) f x = f a • b := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, contractLeft_replaceCoordinate f v a hv y⟩
  · rintro ⟨b, hb⟩
    have hb0 : CliffordAlgebra.contractLeft (Q := 0) f b = 0 := by
      apply ha
      change f a • CliffordAlgebra.contractLeft (Q := 0) f b = f a • 0
      rw [smul_zero, ← map_smul, ← hb, CliffordAlgebra.contractLeft_contractLeft]
    refine ⟨x + ι S (v - a) * b, ?_⟩
    rw [map_replaceCoordinate, map_add, CliffordAlgebra.contractLeft_ι_mul,
      hb, hb0, mul_zero, sub_zero]
    simp only [map_sub, hv, sub_smul, one_smul, add_sub_cancel]
    abel

/-- Congruent values on coefficients and degree-one generators give congruent
values on the whole exterior algebra. The common modulus is central. -/
theorem map_difference_divisible
    (F H : ExteriorAlgebra S M →+* ExteriorAlgebra S M) (t : S)
    (hscalar : ∀ c : S, ∃ b,
      F (algebraMap S (ExteriorAlgebra S M) c) -
        H (algebraMap S (ExteriorAlgebra S M) c) = t • b)
    (hvector : ∀ m : M, ∃ b, F (ι S m) - H (ι S m) = t • b)
    (x : ExteriorAlgebra S M) : ∃ b, F x - H x = t • b := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => exact hscalar c
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    simpa only [map_add, smul_add, ← ha, ← hb] using
      (add_sub_add_comm (F x) (F y) (H x) (H y))
  | ι_mul x m hx =>
    obtain ⟨a, ha⟩ := hvector m
    obtain ⟨b, hb⟩ := hx
    refine ⟨a * F x + H (ι S m) * b, ?_⟩
    simp only [map_mul]
    calc
      _ = (F (ι S m) - H (ι S m)) * F x +
          H (ι S m) * (F x - H x) := by simp only [sub_mul, mul_sub]; abel
      _ = _ := by rw [ha, hb, smul_add, smul_mul_assoc, mul_smul_comm]

end ExteriorAlgebra

open scoped BigOperators

namespace TorusLinkHomology.CoefficientComplex

/-- Extract the first odd coordinate in the old complex. -/
def firstCoordinate (r : ℕ) : Module.Dual (R (r + 1)) (V (r + 1)) :=
  Finsupp.lapply 0

/-- The distinguished generator `χ_ell` in the old complex, as a vector. -/
def firstVector (r : ℕ) : V (r + 1) := Finsupp.single 0 1

@[simp] theorem firstCoordinate_firstVector (r : ℕ) :
    firstCoordinate r (firstVector r) = 1 := by
  simp [firstCoordinate, firstVector]

/-- Rotate the new initial generators into their common old coordinates. -/
def rotateCoordinates (r : ℕ) : V (r + 1) ≃ₗ[R (r + 1)] V (r + 1) :=
  Finsupp.domLCongr (finRotate (r + 1))

@[simp] theorem rotateCoordinates_single_last (r : ℕ) (c : R (r + 1)) :
    rotateCoordinates r (Finsupp.single (Fin.last r) c) = Finsupp.single 0 c := by
  simp [rotateCoordinates]

@[simp] theorem rotateCoordinates_single_castSucc (r : ℕ) (i : Fin r) (c : R (r + 1)) :
    rotateCoordinates r (Finsupp.single i.castSucc c) = Finsupp.single i.succ c := by
  rw [rotateCoordinates, Finsupp.domLCongr_single]
  congr 1
  exact finRotate_of_lt i.isLt

@[simp] theorem tailVector_initial (N r ell : ℕ) (i : Fin r) :
    tailVector N r ell (ell + i.val + 1) = Finsupp.single i 1 := by
  unfold tailVector
  rw [tail_initial]
  exact ExteriorAlgebra.ι_leftInverse _

/-- The comparison is a rotation followed by replacement of one coordinate. -/
theorem JLinear_factorization (N r ell : ℕ) :
    JLinear N (r + 1) (ell + 1) =
      (ExteriorAlgebra.replaceCoordinate (firstCoordinate r) (firstVector r)
        (tailVector N (r + 1) ell (ell + r + 2))).comp
          (rotateCoordinates r).toLinearMap := by
  apply Finsupp.lhom_ext
  intro i c
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [JLinear, Finsupp.linearCombination_single, LinearMap.comp_apply,
      LinearEquiv.coe_coe, rotateCoordinates_single_last]
    have heq : ell + 1 - 1 = ell := by omega
    rw [heq]
    have hind : ell + 1 + (Fin.last r).val + 1 = ell + r + 2 := by simp; omega
    rw [hind]
    simp [ExteriorAlgebra.replaceCoordinate, firstCoordinate, firstVector,
      smul_sub, Finsupp.smul_single]
  · simp only [JLinear, Finsupp.linearCombination_single, LinearMap.comp_apply,
      LinearEquiv.coe_coe, rotateCoordinates_single_castSucc]
    have heq : ell + 1 - 1 = ell := by omega
    rw [heq]
    have hind : ell + 1 + i.castSucc.val + 1 = ell + i.succ.val + 1 := by simp; omega
    rw [hind, tailVector_initial]
    simp [ExteriorAlgebra.replaceCoordinate, firstCoordinate, Finsupp.smul_single]

theorem J_factorization (N r ell : ℕ) (a : A (r + 1)) :
    J N (r + 1) (ell + 1) a =
      ExteriorAlgebra.map
        (ExteriorAlgebra.replaceCoordinate (firstCoordinate r) (firstVector r)
          (tailVector N (r + 1) ell (ell + r + 2)))
        (ExteriorAlgebra.map (rotateCoordinates r).toLinearMap a) := by
  rw [J, JLinear_factorization, ← ExteriorAlgebra.map_comp_map]
  rfl

theorem tailVector_eq_of_gt (N r ell j : ℕ) (hj : ell + r < j) :
    tailVector N r ell j =
      invNat r j • ∑ i : Fin r,
        ((((N + 1 : ℕ) : R r) * ((i.val + 1 : ℕ) : R r) - (j : R r)) * e r i) •
          tailVector N r ell (j - (i.val + 1)) := by
  unfold tailVector
  rw [tail_eq_of_gt _ _ _ _ hj, map_smul, map_sum]
  simp only [map_smul]

/-- The coefficient controlling injectivity of J is `(Nr-ell)/L` times
the final polynomial variable. -/
theorem firstCoordinate_tailVector_boundary (N r ell : ℕ) :
    firstCoordinate r (tailVector N (r + 1) ell (ell + r + 2)) =
      invNat (r + 1) (ell + r + 2) *
        (((N + 1 : ℕ) : R (r + 1)) * ((r + 1 : ℕ) : R (r + 1)) -
          ((ell + r + 2 : ℕ) : R (r + 1))) * e (r + 1) (Fin.last r) := by
  classical
  rw [tailVector_eq_of_gt _ _ _ _ (by omega), map_smul, map_sum]
  have hterm (i : Fin (r + 1)) :
      firstCoordinate r (tailVector N (r + 1) ell (ell + r + 2 - (i.val + 1))) =
        if i = Fin.last r then 1 else 0 := by
    have hind : ell + r + 2 - (i.val + 1) = ell + i.rev.val + 1 := by
      have := i.isLt
      simp only [Fin.val_rev]
      omega
    rw [hind, tailVector_initial]
    simp [firstCoordinate, Finsupp.single_apply, Fin.rev_eq_iff]
  simp only [map_smul, hterm, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [mul_assoc]

theorem exterior_smul_injective (r : ℕ) (c : R r) (hc : c ≠ 0) :
    Function.Injective (fun a : A r => c • a) := by
  let b := (Finsupp.basisSingleOne : Module.Basis (Fin r) (R r) (V r)).ExteriorAlgebra
  intro x y hxy
  apply b.repr.injective
  apply Finsupp.ext
  intro s
  have hs := congrArg (fun z => b.repr z s) hxy
  exact mul_left_cancel₀ hc (by simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using hs)

theorem firstCoordinate_tailVector_boundary_ne_zero (N r ell : ℕ)
    (hm : ell + 1 < N * (r + 1)) :
    firstCoordinate r (tailVector N (r + 1) ell (ell + r + 2)) ≠ 0 := by
  rw [firstCoordinate_tailVector_boundary]
  apply mul_ne_zero
  · apply mul_ne_zero
    · have h := invNat_mul_nat (r + 1) (ell + r + 2) (by omega)
      intro hzero
      rw [hzero, zero_mul] at h
      exact zero_ne_one h
    · have heq :
        ((N + 1 : ℕ) : R (r + 1)) * ((r + 1 : ℕ) : R (r + 1)) -
            ((ell + r + 2 : ℕ) : R (r + 1)) =
          ((N * (r + 1) - (ell + 1) : ℕ) : R (r + 1)) := by
        rw [Nat.cast_sub (Nat.le_of_lt hm)]
        push_cast
        ring
      rw [heq]
      intro hzero
      have hq := congrArg (MvPolynomial.constantCoeff) hzero
      have hn : (N * (r + 1) - (ell + 1) : ℕ) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hm)
      exact (Nat.cast_ne_zero.mpr hn : ((N * (r + 1) - (ell + 1) : ℕ) : ℚ) ≠ 0) (by simpa using hq)
  · exact MvPolynomial.X_ne_zero _

/-- Injectivity of the comparison on chains, including rank one. -/
theorem J_injective (N r ell : ℕ) (hm : ell + 1 < N * (r + 1)) :
    Function.Injective (J N (r + 1) (ell + 1)) := by
  have hreplace := ExteriorAlgebra.map_replaceCoordinate_injective
    (firstCoordinate r) (firstVector r)
    (tailVector N (r + 1) ell (ell + r + 2))
    (firstCoordinate_firstVector r)
    (exterior_smul_injective (r + 1) _
      (firstCoordinate_tailVector_boundary_ne_zero N r ell hm))
  have hrotate : Function.Injective
      (ExteriorAlgebra.map (rotateCoordinates r).toLinearMap) := by
    apply ExteriorAlgebra.map_injective
    refine ⟨(rotateCoordinates r).symm.toLinearMap, ?_⟩
    apply LinearMap.ext
    intro v
    exact (rotateCoordinates r).symm_apply_apply v
  intro x y hxy
  rw [J_factorization, J_factorization] at hxy
  exact hrotate (hreplace hxy)

/-- Delete the first odd coordinate and reduce the last polynomial variable. -/
def dropFirstVector (r : ℕ) :
    V (r + 1) →ₛₗ[(reduceCoefficients r).toRingHom] V r :=
  (Finsupp.linearCombination (R r)
    (Fin.cases 0 (fun i => Finsupp.single i 1))).comp
      (Finsupp.mapRange.linearMap (reduceCoefficients r).toRingHom.toSemilinearMap)

@[simp] theorem dropFirstVector_single_zero (r : ℕ) (c : R (r + 1)) :
    dropFirstVector r (Finsupp.single 0 c) = 0 := by
  change Finsupp.linearCombination (R r) (Fin.cases 0 (fun i => Finsupp.single i 1))
    (Finsupp.mapRange (reduceCoefficients r) (map_zero _) (Finsupp.single 0 c)) = 0
  rw [Finsupp.mapRange_single, Finsupp.linearCombination_single]
  simp

@[simp] theorem dropFirstVector_single_succ (r : ℕ) (i : Fin r) (c : R (r + 1)) :
    dropFirstVector r (Finsupp.single i.succ c) =
      Finsupp.single i (reduceCoefficients r c) := by
  change Finsupp.linearCombination (R r) (Fin.cases 0 (fun i => Finsupp.single i 1))
    (Finsupp.mapRange (reduceCoefficients r) (map_zero _) (Finsupp.single i.succ c)) = _
  rw [Finsupp.mapRange_single, Finsupp.linearCombination_single]
  simp [Finsupp.smul_single]

/-- Reduction on the common exterior subalgebra, extended by killing the
distinguished old generator. -/
def dropFirst (r : ℕ) : A (r + 1) →+* A r :=
  ExteriorAlgebra.mapOfSemilinear (reduceCoefficients r).toRingHom (dropFirstVector r)

@[simp] theorem dropFirst_xi_zero (r : ℕ) : dropFirst r (xi (r + 1) 0) = 0 := by
  rw [dropFirst, xi, ExteriorAlgebra.mapOfSemilinear_iota, dropFirstVector_single_zero, map_zero]

@[simp] theorem dropFirst_xi_succ (r : ℕ) (i : Fin r) :
    dropFirst r (xi (r + 1) i.succ) = xi r i := by
  rw [dropFirst, xi, ExteriorAlgebra.mapOfSemilinear_iota, dropFirstVector_single_succ, map_one]
  rfl

@[simp] theorem dropFirst_algebraMap (r : ℕ) (c : R (r + 1)) :
    dropFirst r (algebraMap (R (r + 1)) (A (r + 1)) c) =
      algebraMap (R r) (A r) (reduceCoefficients r c) :=
  ExteriorAlgebra.mapOfSemilinear_algebraMap _ _ _

theorem dropFirst_smul (r : ℕ) (c : R (r + 1)) (a : A (r + 1)) :
    dropFirst r (c • a) = reduceCoefficients r c • dropFirst r a :=
  ExteriorAlgebra.mapOfSemilinear_smul _ _ _ _

/-- The projection to the shifted quotient, in unshifted chain notation. -/
def p (r : ℕ) (a : A (r + 1)) : A r :=
  dropFirst r (CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r) a)

theorem p_add (r : ℕ) (a b : A (r + 1)) : p r (a + b) = p r a + p r b := by
  simp [p]

theorem p_smul (r : ℕ) (c : R (r + 1)) (a : A (r + 1)) :
    p r (c • a) = reduceCoefficients r c • p r a := by
  simp only [p, map_smul, dropFirst_smul]

/-- The first contraction anticommutes with the differential; deleting the
first coordinate afterward removes the extra first-coordinate equation. -/
theorem p_d (N r ell : ℕ) (a : A (r + 1)) :
    p r (d N (r + 1) ell a) = -d N r (ell + 1) (p r a) := by
  let ds := differentialFunctional N (r + 1) ell -
    G N (r + 1) (ell + 1) • firstCoordinate r
  have hfun (v : V (r + 1)) :
      differentialFunctional N r (ell + 1) (dropFirstVector r v) =
        reduceCoefficients r (ds v) := by
    suffices h : (differentialFunctional N r (ell + 1)).comp (dropFirstVector r) =
        (reduceCoefficients r).toRingHom.toSemilinearMap.comp ds from
      LinearMap.congr_fun h v
    apply Finsupp.lhom_ext
    intro i c
    simp only [LinearMap.comp_apply]
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [dropFirstVector_single_zero, map_zero]
      change 0 = reduceCoefficients r (ds (Finsupp.single 0 c))
      simp [ds, firstCoordinate, differentialFunctional, mul_comm]
    · rw [dropFirstVector_single_succ]
      change _ = reduceCoefficients r (ds (Finsupp.single i.succ c))
      simp [ds, firstCoordinate, differentialFunctional, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hnat := ExteriorAlgebra.contractLeft_mapOfSemilinear
    (reduceCoefficients r).toRingHom (dropFirstVector r) ds
    (differentialFunctional N r (ell + 1)) hfun
    (CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r) a)
  have hds : CliffordAlgebra.contractLeft (Q := 0) ds
      (CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r) a) =
        d N (r + 1) ell
          (CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r) a) := by
    simp [ds, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      CliffordAlgebra.contractLeft_contractLeft, d, dga]
  change dropFirst r ((CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r))
      (CliffordAlgebra.contractLeft (Q := 0) (differentialFunctional N (r + 1) ell) a)) = _
  rw [CliffordAlgebra.contractLeft_comm, map_neg]
  congr 1
  change _ = CliffordAlgebra.contractLeft (Q := 0) (differentialFunctional N r (ell + 1)) _
  rw [hds] at hnat
  exact hnat.symm

/-- The image of J lies in the kernel of the shifted projection. -/
theorem p_J (N r ell : ℕ) (a : A (r + 1)) :
    p r (J N (r + 1) (ell + 1) a) = 0 := by
  rw [p, J_factorization,
    ExteriorAlgebra.contractLeft_replaceCoordinate _ _ _ (firstCoordinate_firstVector r),
    dropFirst_smul, firstCoordinate_tailVector_boundary]
  simp only [map_mul, reduceCoefficients_e_last, mul_zero, zero_smul]

/-- Lift quotient odd generators to the common old generators. -/
def includeCommonVector (r : ℕ) :
    V r →ₛₗ[(includeCoefficients r).toRingHom] V (r + 1) :=
  (Finsupp.linearCombination (R (r + 1))
    (fun i : Fin r => Finsupp.single i.succ 1)).comp
      (Finsupp.mapRange.linearMap (includeCoefficients r).toRingHom.toSemilinearMap)

@[simp] theorem includeCommonVector_single (r : ℕ) (i : Fin r) (c : R r) :
    includeCommonVector r (Finsupp.single i c) =
      Finsupp.single i.succ (includeCoefficients r c) := by
  change Finsupp.linearCombination (R (r + 1)) (fun i : Fin r => Finsupp.single i.succ 1)
    (Finsupp.mapRange (includeCoefficients r) (map_zero _) (Finsupp.single i c)) = _
  rw [Finsupp.mapRange_single, Finsupp.linearCombination_single]
  simp [Finsupp.smul_single]

/-- A coefficientwise section of reduction on the common exterior algebra. -/
def includeCommon (r : ℕ) : A r →+* A (r + 1) :=
  ExteriorAlgebra.mapOfSemilinear (includeCoefficients r).toRingHom (includeCommonVector r)

@[simp] theorem includeCommon_iota (r : ℕ) (v : V r) :
    includeCommon r (ExteriorAlgebra.ι (R r) v) =
      ExteriorAlgebra.ι (R (r + 1)) (includeCommonVector r v) :=
  ExteriorAlgebra.mapOfSemilinear_iota _ _ _

@[simp] theorem includeCommon_xi (r : ℕ) (i : Fin r) :
    includeCommon r (xi r i) = xi (r + 1) i.succ := by
  rw [xi, includeCommon_iota, includeCommonVector_single, map_one]
  rfl

@[simp] theorem includeCommon_algebraMap (r : ℕ) (c : R r) :
    includeCommon r (algebraMap (R r) (A r) c) =
      algebraMap (R (r + 1)) (A (r + 1)) (includeCoefficients r c) :=
  ExteriorAlgebra.mapOfSemilinear_algebraMap _ _ _

theorem includeCommon_smul (r : ℕ) (c : R r) (a : A r) :
    includeCommon r (c • a) = includeCoefficients r c • includeCommon r a :=
  ExteriorAlgebra.mapOfSemilinear_smul _ _ _ _

theorem dropFirstVector_includeCommonVector (r : ℕ) (v : V r) :
    dropFirstVector r (includeCommonVector r v) = v := by
  induction v using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add i c v _ _ hv =>
    rw [map_add, map_add, includeCommonVector_single, dropFirstVector_single_succ,
      reduceCoefficients_include, hv]

@[simp] theorem dropFirst_includeCommon (r : ℕ) (a : A r) :
    dropFirst r (includeCommon r a) = a := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap c => rw [includeCommon_algebraMap, dropFirst_algebraMap, reduceCoefficients_include]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    rw [map_mul, map_mul, includeCommon_iota, hx]
    change ExteriorAlgebra.mapOfSemilinear _ _ _ * x = _
    rw [ExteriorAlgebra.mapOfSemilinear_iota, dropFirstVector_includeCommonVector]

theorem firstCoordinate_includeCommonVector (r : ℕ) (v : V r) :
    firstCoordinate r (includeCommonVector r v) = 0 := by
  induction v using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add i c v _ _ hv =>
    rw [map_add, map_add, includeCommonVector_single, hv]
    simp [firstCoordinate]

theorem contractLeft_includeCommon (r : ℕ) (a : A r) :
    CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r) (includeCommon r a) = 0 := by
  have h := ExteriorAlgebra.contractLeft_mapOfSemilinear
    (includeCoefficients r).toRingHom (includeCommonVector r) 0 (firstCoordinate r)
    (fun v => by simpa only [LinearMap.zero_apply, map_zero] using
      firstCoordinate_includeCommonVector r v) a
  change CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r)
    (ExteriorAlgebra.mapOfSemilinear (includeCoefficients r).toRingHom (includeCommonVector r) a) = 0
  simpa only [map_zero, LinearMap.zero_apply] using h

/-- Every quotient chain has the explicit lift `χ_ell` times its common lift. -/
theorem p_lift (r : ℕ) (a : A r) :
    p r (xi (r + 1) 0 * includeCommon r a) = a := by
  rw [p, xi, CliffordAlgebra.contractLeft_ι_mul, contractLeft_includeCommon]
  have h : firstCoordinate r (Finsupp.single 0 1) = 1 := by simp [firstCoordinate]
  rw [h, one_smul, mul_zero, sub_zero, dropFirst_includeCommon]

theorem p_surjective (r : ℕ) : Function.Surjective (p r) :=
  fun a => ⟨xi (r + 1) 0 * includeCommon r a, p_lift r a⟩

/-- Projection to chains without the distinguished generator. -/
def commonProjection (r : ℕ) : A (r + 1) →ₐ[R (r + 1)] A (r + 1) :=
  ExteriorAlgebra.map (ExteriorAlgebra.contractionProjection (firstCoordinate r) (firstVector r))

@[simp] theorem commonProjection_xi_zero (r : ℕ) :
    commonProjection r (xi (r + 1) 0) = 0 := by
  simp [commonProjection, xi, firstCoordinate, firstVector]

@[simp] theorem commonProjection_xi_succ (r : ℕ) (i : Fin r) :
    commonProjection r (xi (r + 1) i.succ) = xi (r + 1) i.succ := by
  simp [commonProjection, xi, firstCoordinate, firstVector]

/-- Reduction followed by the coefficientwise section differs from the common
projection by a multiple of the final polynomial variable. -/
theorem common_remainder_divisible (r : ℕ) (x : A (r + 1)) :
    ∃ b, commonProjection r x - includeCommon r (dropFirst r x) =
      e (r + 1) (Fin.last r) • b := by
  apply ExteriorAlgebra.map_difference_divisible
    (commonProjection r).toRingHom ((includeCommon r).comp (dropFirst r))
  · intro c
    obtain ⟨b, hb⟩ := coefficient_remainder_divisible r c
    refine ⟨algebraMap (R (r + 1)) (A (r + 1)) b, ?_⟩
    change commonProjection r (algebraMap _ _ c) -
      includeCommon r (dropFirst r (algebraMap _ _ c)) = _
    rw [AlgHom.commutes, dropFirst_algebraMap, includeCommon_algebraMap, ← map_sub, hb,
      map_mul, Algebra.smul_def]
  · intro v
    change ∃ b, commonProjection r (ExteriorAlgebra.ι (R (r + 1)) v) -
      includeCommon r (dropFirst r (ExteriorAlgebra.ι (R (r + 1)) v)) = _
    induction v using Finsupp.induction with
    | zero => exact ⟨0, by simp⟩
    | @single_add i c v _ _ hv =>
      obtain ⟨b, hb⟩ := hv
      have hsingle : ∃ b, commonProjection r
          (ExteriorAlgebra.ι (R (r + 1)) (Finsupp.single i c)) -
          includeCommon r (dropFirst r
            (ExteriorAlgebra.ι (R (r + 1)) (Finsupp.single i c))) =
          e (r + 1) (Fin.last r) • b := by
        have hi : ExteriorAlgebra.ι (R (r + 1)) (Finsupp.single i c) =
            c • xi (r + 1) i := by simp [xi, ← map_smul, Finsupp.smul_single]
        rw [hi, map_smul, dropFirst_smul, includeCommon_smul]
        refine Fin.cases ?_ (fun i => ?_) i
        · exact ⟨0, by rw [commonProjection_xi_zero, dropFirst_xi_zero, map_zero]; simp⟩
        · obtain ⟨b, hb⟩ := coefficient_remainder_divisible r c
          refine ⟨b • xi (r + 1) i.succ, ?_⟩
          rw [commonProjection_xi_succ, dropFirst_xi_succ, includeCommon_xi, ← sub_smul,
            hb, mul_smul]
      obtain ⟨a, ha⟩ := hsingle
      refine ⟨a + b, ?_⟩
      simp only [map_add, smul_add]
      rw [add_sub_add_comm, ha, hb]

/-- On the common exterior subalgebra the only kernel of coefficient
reduction consists of multiples of the final polynomial variable. -/
theorem dropFirst_eq_zero_iff_of_contract_eq_zero (r : ℕ) (x : A (r + 1))
    (hx : CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r) x = 0) :
    dropFirst r x = 0 ↔ ∃ b, x = e (r + 1) (Fin.last r) • b := by
  constructor
  · intro hzero
    obtain ⟨b, hb⟩ := common_remainder_divisible r x
    refine ⟨b, ?_⟩
    simpa only [commonProjection, ExteriorAlgebra.map_contractionProjection, hx,
      hzero, map_zero, mul_zero, sub_zero] using hb
  · rintro ⟨b, rfl⟩
    rw [dropFirst_smul, reduceCoefficients_e_last, zero_smul]

theorem mem_range_J_iff (N r ell : ℕ) (hm : ell + 1 < N * (r + 1))
    (x : A (r + 1)) :
    (∃ y, J N (r + 1) (ell + 1) y = x) ↔
      ∃ b, CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r) x =
        firstCoordinate r (tailVector N (r + 1) ell (ell + r + 2)) • b := by
  have h := ExteriorAlgebra.mem_range_map_replaceCoordinate_iff
    (firstCoordinate r) (firstVector r)
    (tailVector N (r + 1) ell (ell + r + 2))
    (firstCoordinate_firstVector r)
    (exterior_smul_injective (r + 1) _
      (firstCoordinate_tailVector_boundary_ne_zero N r ell hm)) x
  constructor
  · rintro ⟨y, hy⟩
    exact h.mp ⟨ExteriorAlgebra.map (rotateCoordinates r).toLinearMap y,
      (J_factorization N r ell y).symm.trans hy⟩
  · intro hx
    obtain ⟨z, hz⟩ := h.mpr hx
    have hs : Function.Surjective (ExteriorAlgebra.map (rotateCoordinates r).toLinearMap) :=
      ExteriorAlgebra.map_surjective_iff.mpr (rotateCoordinates r).surjective
    obtain ⟨y, hy⟩ := hs z
    exact ⟨y, by rw [J_factorization, hy, hz]⟩

/-- Only a nonzero rational scalar separates the distinguished coefficient
of the comparison from the final polynomial variable. -/
theorem boundary_coefficient_rescale (N r ell : ℕ) (hm : ell + 1 < N * (r + 1)) :
    (((ell + r + 2 : ℕ) : R (r + 1)) *
      invNat (r + 1) (N * (r + 1) - (ell + 1))) *
        firstCoordinate r (tailVector N (r + 1) ell (ell + r + 2)) =
      e (r + 1) (Fin.last r) := by
  rw [firstCoordinate_tailVector_boundary]
  have heq :
      ((N + 1 : ℕ) : R (r + 1)) * ((r + 1 : ℕ) : R (r + 1)) -
          ((ell + r + 2 : ℕ) : R (r + 1)) =
        ((N * (r + 1) - (ell + 1) : ℕ) : R (r + 1)) := by
    rw [Nat.cast_sub (Nat.le_of_lt hm)]
    push_cast
    ring
  rw [heq]
  calc
    _ = (((ell + r + 2 : ℕ) : R (r + 1)) * invNat (r + 1) (ell + r + 2)) *
        (invNat (r + 1) (N * (r + 1) - (ell + 1)) *
          ((N * (r + 1) - (ell + 1) : ℕ) : R (r + 1))) *
        e (r + 1) (Fin.last r) := by ring
    _ = _ := by
      rw [nat_mul_invNat _ _ (by omega), invNat_mul_nat _ _ (by omega), one_mul, one_mul]

/-- Exactness on chains: the kernel of p is exactly the image of J. -/
theorem p_eq_zero_iff (N r ell : ℕ) (hm : ell + 1 < N * (r + 1))
    (x : A (r + 1)) :
    p r x = 0 ↔ ∃ y, J N (r + 1) (ell + 1) y = x := by
  constructor
  · intro hx
    obtain ⟨b, hb⟩ :=
      (dropFirst_eq_zero_iff_of_contract_eq_zero r
        (CliffordAlgebra.contractLeft (Q := 0) (firstCoordinate r) x)
        (CliffordAlgebra.contractLeft_contractLeft _ _)).mp hx
    apply (mem_range_J_iff N r ell hm x).mpr
    refine ⟨((((ell + r + 2 : ℕ) : R (r + 1)) *
      invNat (r + 1) (N * (r + 1) - (ell + 1))) • b), ?_⟩
    rw [smul_smul, mul_comm, boundary_coefficient_rescale N r ell hm, hb]
  · rintro ⟨y, rfl⟩
    exact p_J N r ell y

/-- A lift of a quotient cycle has differential in the image of J, and its
unique preimage is a cycle. This constructs connecting representatives. -/
theorem connecting_representative (N r ell : ℕ) (hm : ell + 1 < N * (r + 1))
    (a : A r) (ha : d N r (ell + 1) a = 0) :
    ∃ z : A (r + 1), d N (r + 1) (ell + 1) z = 0 ∧
      J N (r + 1) (ell + 1) z =
        d N (r + 1) ell (xi (r + 1) 0 * includeCommon r a) := by
  have hzero : p r (d N (r + 1) ell (xi (r + 1) 0 * includeCommon r a)) = 0 := by
    rw [p_d, p_lift, ha, neg_zero]
  obtain ⟨z, hz⟩ := (p_eq_zero_iff N r ell hm _).mp hzero
  refine ⟨z, ?_, hz⟩
  apply J_injective N r ell hm
  have hchain := d_J N (r + 1) (ell + 1) z
  simp only [Nat.add_sub_cancel_right] at hchain
  rw [← hchain, hz, d_squared, map_zero]

/-- The connecting construction works with any chosen lift of a quotient
cycle. Its preimage under J is unique by `J_injective`. -/
theorem connecting_representative_of_lift (N r ell : ℕ)
    (hm : ell + 1 < N * (r + 1)) (w : A (r + 1))
    (hw : d N r (ell + 1) (p r w) = 0) :
    ∃ z : A (r + 1), d N (r + 1) (ell + 1) z = 0 ∧
      J N (r + 1) (ell + 1) z = d N (r + 1) ell w := by
  have hzero : p r (d N (r + 1) ell w) = 0 := by rw [p_d, hw, neg_zero]
  obtain ⟨z, hz⟩ := (p_eq_zero_iff N r ell hm _).mp hzero
  refine ⟨z, ?_, hz⟩
  apply J_injective N r ell hm
  have hchain := d_J N (r + 1) (ell + 1) z
  simp only [Nat.add_sub_cancel_right] at hchain
  rw [← hchain, hz, d_squared, map_zero]

end TorusLinkHomology.CoefficientComplex
