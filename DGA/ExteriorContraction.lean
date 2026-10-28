import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# The differential on an exterior algebra

Contraction by a linear functional lowers exterior degree by one and satisfies
the signed Leibniz rule. These facts give the usual Koszul differential.
-/

namespace ExteriorAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable (f : Module.Dual R M)

local notation "δ" => CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) f

/-- Contraction vanishes on exterior degree zero. -/
theorem contractLeft_eq_zero_of_mem_degree_zero {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^0 M) : δ x = 0 := by
  rw [show (⋀[R]^0 M) = 1 by rfl] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
  exact CliffordAlgebra.contractLeft_algebraMap _ _ _

private theorem contractLeft_degree {p : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^p M) :
    match p with
    | 0 => δ x = 0
    | k + 1 => δ x ∈ ⋀[R]^k M := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap => exact CliffordAlgebra.contractLeft_algebraMap _ _ _
  | add x y p hx hy ihx ihy =>
    cases p with
    | zero => simp only [map_add, ihx, ihy, add_zero]
    | succ p => simpa only [map_add] using (⋀[R]^p M).add_mem ihx ihy
  | mem_mul a ha p x hx ih =>
    obtain ⟨a, rfl⟩ := ha
    rw [CliffordAlgebra.contractLeft_ι_mul]
    apply Submodule.sub_mem
    · exact (⋀[R]^p M).smul_mem (f a) hx
    · cases p with
      | zero => simpa only [ih, mul_zero] using (⋀[R]^0 M).zero_mem
      | succ p =>
        change CliffordAlgebra.ι (0 : QuadraticForm R M) a * δ x ∈
          (LinearMap.range (ι R)) ^ (p + 1)
        rw [pow_succ']
        exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ a) ih

/-- Contraction lowers positive exterior degree by one. -/
theorem contractLeft_mem {p : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^(p + 1) M) : δ x ∈ ⋀[R]^p M :=
  contractLeft_degree f hx

/-- The graded Leibniz rule for contraction, with an arbitrary second factor. -/
theorem contractLeft_mul_of_mem {p : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^p M) (y : ExteriorAlgebra R M) :
    δ (x * y) = δ x * y + (-1 : ℤ)^p • (x * δ y) := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap =>
    simp only [CliffordAlgebra.contractLeft_algebraMap_mul,
      CliffordAlgebra.contractLeft_algebraMap, zero_mul, zero_add, pow_zero, one_smul]
  | add x x' p hx hx' ihx ihx' =>
    simp only [add_mul, map_add, ihx, ihx', smul_add]
    abel
  | mem_mul a ha p x hx ih =>
    obtain ⟨a, rfl⟩ := ha
    rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul, ih,
      CliffordAlgebra.contractLeft_ι_mul]
    simp only [mul_add, sub_mul, smul_mul_assoc, mul_smul_comm, mul_assoc,
      pow_succ, mul_neg, mul_one, neg_smul]
    abel

end ExteriorAlgebra
