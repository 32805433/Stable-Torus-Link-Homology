import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! # Exterior maps with a change of coefficient ring -/

noncomputable section

namespace ExteriorAlgebra

section ScalarChange

variable {S T M P : Type*} [CommRing S] [CommRing T]
  [AddCommGroup M] [Module S M] [AddCommGroup P] [Module T P]

/-- The exterior map induced by a semilinear map and its coefficient homomorphism. -/
def mapOfSemilinear (f : S →+* T) (g : M →ₛₗ[f] P) :
    ExteriorAlgebra S M →+* ExteriorAlgebra T P := by
  letI : Algebra S (ExteriorAlgebra T P) :=
    Algebra.compHom (ExteriorAlgebra T P) f
  let g' : M →ₗ[S] ExteriorAlgebra T P :=
    { toFun := fun m => ExteriorAlgebra.ι T (g m)
      map_add' := by intro x y; simp
      map_smul' := by
        intro s m
        rw [g.map_smulₛₗ, map_smul]
        change f s • ExteriorAlgebra.ι T (g m) =
          algebraMap T (ExteriorAlgebra T P) (f s) * ExteriorAlgebra.ι T (g m)
        rw [Algebra.smul_def] }
  exact (ExteriorAlgebra.lift S ⟨g', fun m => ExteriorAlgebra.ι_sq_zero (g m)⟩).toRingHom

theorem mapOfSemilinear_iota (f : S →+* T) (g : M →ₛₗ[f] P) (m : M) :
    mapOfSemilinear f g (ExteriorAlgebra.ι S m) = ExteriorAlgebra.ι T (g m) := by
  simp [mapOfSemilinear]

theorem mapOfSemilinear_algebraMap (f : S →+* T) (g : M →ₛₗ[f] P) (s : S) :
    mapOfSemilinear f g (algebraMap S (ExteriorAlgebra S M) s) =
      algebraMap T (ExteriorAlgebra T P) (f s) := by
  simp [mapOfSemilinear]
  rfl

theorem mapOfSemilinear_smul (f : S →+* T) (g : M →ₛₗ[f] P)
    (s : S) (x : ExteriorAlgebra S M) :
    mapOfSemilinear f g (s • x) = f s • mapOfSemilinear f g x := by
  rw [Algebra.smul_def, map_mul, mapOfSemilinear_algebraMap, Algebra.smul_def]

theorem contractLeft_mapOfSemilinear (f : S →+* T) (g : M →ₛₗ[f] P)
    (ds : Module.Dual S M) (dt : Module.Dual T P)
    (h : ∀ m, dt (g m) = f (ds m)) (x : ExteriorAlgebra S M) :
    CliffordAlgebra.contractLeft (Q := 0) dt (mapOfSemilinear f g x) =
      mapOfSemilinear f g (CliffordAlgebra.contractLeft (Q := 0) ds x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap s =>
    rw [mapOfSemilinear_algebraMap, CliffordAlgebra.contractLeft_algebraMap,
      CliffordAlgebra.contractLeft_algebraMap, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul m x hx =>
    simp only [map_mul, mapOfSemilinear_iota, CliffordAlgebra.contractLeft_ι_mul,
      map_sub, mapOfSemilinear_smul, hx, h]

end ScalarChange

end ExteriorAlgebra
