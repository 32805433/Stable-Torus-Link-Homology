import DGA
import DGA.ExteriorContraction

/-!
# Exterior algebras with a contraction differential

The exterior-degree grading is extended by zero to negative integer degrees.
Together with contraction by a linear functional, this makes the exterior
algebra a Koszul DGA. The square-zero identity is supplied by mathlib.
-/

noncomputable section

namespace ExteriorAlgebra

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- Exterior degree, regarded as an integer grading and zero in negative degrees. -/
def intGrading (p : ℤ) : Submodule R (ExteriorAlgebra R M) :=
  if 0 ≤ p then ⋀[R]^p.toNat M else ⊥

@[simp] theorem intGrading_natCast (p : ℕ) :
    intGrading R M (p : ℤ) = ⋀[R]^p M := by
  simp [intGrading]

theorem intGrading_of_neg {p : ℤ} (hp : p < 0) : intGrading R M p = ⊥ := by
  simp [intGrading, not_le.mpr hp]

instance intGrading_gradedMonoid : SetLike.GradedMonoid (intGrading R M) where
  one_mem := by simp [intGrading]
  mul_mem := by
    intro i j x y hx hy
    by_cases hi : 0 ≤ i
    · by_cases hj : 0 ≤ j
      · simp only [intGrading, if_pos hi] at hx
        simp only [intGrading, if_pos hj] at hy
        simpa [intGrading, add_nonneg hi hj, Int.toNat_add hi hj] using
          (SetLike.mul_mem_graded hx hy)
      · have hy0 : y = 0 := by simpa [intGrading, hj] using hy
        simp [hy0]
    · have hx0 : x = 0 := by simpa [intGrading, hi] using hx
      simp [hx0]

open scoped DirectSum

/-- The exterior generators embedded in integer degree one. -/
private def intGradedIota : M →ₗ[R] ⨁ i : ℤ, intGrading R M i :=
  DirectSum.lof R ℤ (fun i => intGrading R M i) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by
      simp [intGrading, pow_one]

private theorem intGradedIota_sq_zero (m : M) :
    intGradedIota R M m * intGradedIota R M m = 0 := by
  change DirectSum.of _ 1 _ * DirectSum.of _ 1 _ = 0
  rw [DirectSum.of_mul_of]
  exact DFinsupp.single_eq_zero.mpr (Subtype.ext (ExteriorAlgebra.ι_sq_zero m))

/-- The decomposition map into integer exterior degrees. -/
private def intGradedLift : ExteriorAlgebra R M →ₐ[R] ⨁ i : ℤ, intGrading R M i :=
  lift R ⟨intGradedIota R M, intGradedIota_sq_zero R M⟩

private theorem intGradedLift_nat (i : ℕ) (x : ⋀[R]^i M) :
    intGradedLift R M (x : ExteriorAlgebra R M) =
      DirectSum.of (fun j : ℤ => intGrading R M j) (i : ℤ)
        ⟨x, by simp⟩ := by
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap =>
    simp_rw [AlgHom.commutes, DirectSum.algebraMap_apply]
    rfl
  | add _ _ _ _ _ ihx ihy =>
    simp_rw [map_add, ihx, ihy, ← map_add]
    rfl
  | mem_mul _ hm _ _ _ ih =>
    obtain ⟨_, rfl⟩ := hm
    simp_rw [map_mul, ih, intGradedLift, lift_ι_apply, intGradedIota,
      LinearMap.comp_apply, DirectSum.lof_eq_of, DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq
      (Sigma.subtype_ext (by simp [GradedMonoid.mk, add_comm]) rfl)

private theorem intGradedLift_eq (i : ℤ) (x : intGrading R M i) :
    intGradedLift R M (x : ExteriorAlgebra R M) =
      DirectSum.of (fun j : ℤ => intGrading R M j) i x := by
  by_cases hi : 0 ≤ i
  · lift i to ℕ using hi
    exact intGradedLift_nat R M i ⟨x, by simpa using x.property⟩
  · have hx : x = 0 := by
      apply Subtype.ext
      simpa [intGrading, hi] using x.property
    simp [hx]

/-- The integer exterior-degree grading is an internal graded algebra. -/
instance intGradedAlgebra : GradedAlgebra (intGrading R M) :=
  GradedAlgebra.ofAlgHom _ (intGradedLift R M)
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.comp_apply, AlgHom.id_apply, intGradedLift]
      rw [lift_ι_apply]
      change DirectSum.coeAlgHom _ (DirectSum.of _ 1 _) = _
      rw [DirectSum.coeAlgHom_of]
      rfl)
    (intGradedLift_eq R M)

/-- The Koszul DGA of a linear functional: its differential is contraction.

Taking `M` to be a free module and `f` to send its basis vectors to a sequence
of coefficients gives the Koszul differential associated to that sequence.
-/
def koszulDGA (f : Module.Dual R M) : DGA R (ExteriorAlgebra R M) where
  grading := intGrading R M
  gradedAlgebra := inferInstance
  d := CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) f
  d_squared := CliffordAlgebra.contractLeft_contractLeft f
  d_mem := by
    intro p x hx
    by_cases hp : 0 ≤ p
    · lift p to ℕ using hp
      have hx' : x ∈ ⋀[R]^p M := by simpa using hx
      cases p with
      | zero =>
        rw [contractLeft_eq_zero_of_mem_degree_zero f hx']
        exact Submodule.zero_mem _
      | succ p =>
        simpa using (contractLeft_mem f hx')
    · have hx0 : x = 0 := by simpa [intGrading, hp] using hx
      simp [hx0]
  leibniz := by
    intro p x hx y
    by_cases hp : 0 ≤ p
    · lift p to ℕ using hp
      have hx' : x ∈ ⋀[R]^p M := by simpa using hx
      simpa only [Int.coe_negOnePow_natCast] using contractLeft_mul_of_mem f hx' y
    · have hx0 : x = 0 := by simpa [intGrading, hp] using hx
      simp [hx0]

@[simp] theorem koszulDGA_d (f : Module.Dual R M) :
    (koszulDGA R M f).d = CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) f :=
  rfl

@[simp] theorem koszulDGA_grading (f : Module.Dual R M) :
    (koszulDGA R M f).grading = intGrading R M := rfl

end ExteriorAlgebra
