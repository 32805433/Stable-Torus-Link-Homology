import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! # Naturality of exterior contraction under linear maps -/

namespace ExteriorAlgebra

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Pulling back the differential functional makes the induced exterior map
commute with the Koszul differentials. -/
theorem contractLeft_map (f : M →ₗ[R] N) (g : Module.Dual R N)
    (x : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := 0) g (map f x) =
      map f (CliffordAlgebra.contractLeft (Q := 0) (g.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul m x hx =>
    simp only [map_mul, map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      map_sub, map_smul, LinearMap.comp_apply, hx]

/-- A generator-level equality of differential functionals gives a chain map. -/
theorem contractLeft_map_of_comp_eq (f : M →ₗ[R] N)
    (g : Module.Dual R N) (h : Module.Dual R M) (hgf : g.comp f = h)
    (x : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := 0) g (map f x) =
      map f (CliffordAlgebra.contractLeft (Q := 0) h x) := by
  rw [contractLeft_map, hgf]

end ExteriorAlgebra
