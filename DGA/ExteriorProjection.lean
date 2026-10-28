import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Splitting cycles of a contraction

If a functional takes the value one on a vector, its kernel generates every
cycle in the exterior algebra. This is the fraction-field step of the
short-length calculation, expressed without a choice of a homogeneous basis.
-/

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Subtract the component along `v` measured by `f`. -/
def contractionProjection (f : Module.Dual R M) (v : M) : M →ₗ[R] M :=
  LinearMap.id - f.smulRight v

@[simp] theorem contractionProjection_apply (f : Module.Dual R M) (v m : M) :
    contractionProjection f v m = m - f m • v := rfl

/-- The induced exterior map is an explicit projection on cycles. The identity
itself does not require `f v = 1`. -/
theorem map_contractionProjection (f : Module.Dual R M) (v : M)
    (x : ExteriorAlgebra R M) :
    map (contractionProjection f v) x =
      x - ι R v * CliffordAlgebra.contractLeft (Q := 0) f x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]; abel
  | ι_mul x m hx =>
    rw [map_mul, map_apply_ι, contractionProjection_apply, map_sub, map_smul, hx]
    rw [CliffordAlgebra.contractLeft_ι_mul]
    have hswap : ι R m * ι R v = -(ι R v * ι R m) :=
      eq_neg_of_add_eq_zero_left (ι_add_mul_swap m v)
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      ← mul_assoc, hswap, neg_mul, ι_sq_zero, zero_mul, smul_zero]
    abel

theorem contractionProjection_mem_ker (f : Module.Dual R M) (v : M)
    (hv : f v = 1) (m : M) : contractionProjection f v m ∈ f.ker := by
  simp [LinearMap.mem_ker, hv]

/-- To generate every cycle it is enough to generate the degree-one kernel,
provided that the functional is split surjective. -/
theorem cycle_mem_subalgebra_of_ker (f : Module.Dual R M) (v : M)
    (hv : f v = 1) (S : Subalgebra R (ExteriorAlgebra R M))
    (hS : ∀ m ∈ f.ker, ι R m ∈ S) (x : ExteriorAlgebra R M)
    (hx : CliffordAlgebra.contractLeft (Q := 0) f x = 0) : x ∈ S := by
  have himage : ∀ y : ExteriorAlgebra R M, map (contractionProjection f v) y ∈ S := by
    intro y
    induction y using CliffordAlgebra.left_induction with
    | algebraMap r => simp
    | add y z hy hz => simpa only [map_add] using S.add_mem hy hz
    | ι_mul y m hy =>
      simpa only [map_mul, map_apply_ι] using
        S.mul_mem (hS _ (contractionProjection_mem_ker f v hv m)) hy
  simpa only [map_contractionProjection, hx, mul_zero, sub_zero] using himage x

end ExteriorAlgebra
