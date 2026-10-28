import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Power series over a possibly noncommutative algebra

Scalar power series remain central even when the coefficient algebra is
noncommutative. Series with exterior-degree-one coefficients anticommute,
and square to zero over the rationals. These are the relations needed to
specialize finite exterior identities into coefficient series.
-/

noncomputable section

namespace PowerSeries

open scoped BigOperators

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem scalarSeries_commutes (f : PowerSeries R) (g : PowerSeries A) :
    map (algebraMap R A) f * g = g * map (algebraMap R A) f := by
  ext n : 1
  simp only [coeff_mul, coeff_map]
  calc
    _ = ∑ ij ∈ Finset.antidiagonal n,
        algebraMap R A (f.coeff ij.2) * g.coeff ij.1 :=
      Finset.Nat.sum_antidiagonal_swap.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ij _
      exact Algebra.commutes _ _

/-- A named algebra structure, so it can be selected locally without
competing with mathlib's instance for commutative target coefficients. -/
@[instance_reducible] def scalarSeriesAlgebra : Algebra (PowerSeries R) (PowerSeries A) :=
  (map (algebraMap R A)).toAlgebra' scalarSeries_commutes

end PowerSeries

namespace ExteriorAlgebra

open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A series whose every coefficient is a degree-one exterior generator. -/
def iotaSeries (v : ℕ → M) : PowerSeries (ExteriorAlgebra R M) :=
  PowerSeries.mk fun i => ι R (v i)

@[simp] theorem coeff_iotaSeries (v : ℕ → M) (i : ℕ) :
    (iotaSeries v).coeff i = ι R (v i) := PowerSeries.coeff_mk _ _

theorem iotaSeries_mul_add_swap (v w : ℕ → M) :
    iotaSeries (R := R) v * iotaSeries w + iotaSeries w * iotaSeries v = 0 := by
  ext n : 1
  simp only [map_add, PowerSeries.coeff_mul, coeff_iotaSeries, map_zero]
  have hswap : (∑ ij ∈ Finset.antidiagonal n, ι R (w ij.1) * ι R (v ij.2)) =
      ∑ ij ∈ Finset.antidiagonal n, ι R (w ij.2) * ι R (v ij.1) :=
    Finset.Nat.sum_antidiagonal_swap.symm
  rw [hswap, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro ij _
  exact ι_add_mul_swap (v ij.1) (w ij.2)

theorem iotaSeries_sq_zero [Algebra ℚ R] (v : ℕ → M) :
    iotaSeries (R := R) v * iotaSeries v = 0 := by
  let : Algebra ℚ (ExteriorAlgebra R M) :=
    Algebra.compHom (ExteriorAlgebra R M) (algebraMap ℚ R)
  have h := iotaSeries_mul_add_swap (R := R) v v
  have hdouble : (2 : ℚ) • (iotaSeries (R := R) v * iotaSeries v) = 0 := by
    simpa only [show (2 : ℚ) = 1 + 1 by norm_num, add_smul, one_smul] using h
  exact (smul_eq_zero.mp hdouble).resolve_left (by norm_num)

section ScalarSeries

local instance : Algebra (PowerSeries R) (PowerSeries (ExteriorAlgebra R M)) :=
  PowerSeries.scalarSeriesAlgebra

/-- Series all of whose coefficients have exterior degree one. -/
def oddSeries : Submodule (PowerSeries R) (PowerSeries (ExteriorAlgebra R M)) where
  carrier := {f | ∀ n, f.coeff n ∈ LinearMap.range (ι R)}
  zero_mem' := by intro n; exact ⟨0, by simp⟩
  add_mem' := by
    intro f g hf hg n
    simpa only [map_add] using (LinearMap.range (ι R)).add_mem (hf n) (hg n)
  smul_mem' := by
    intro f g hg n
    change (PowerSeries.map (algebraMap R (ExteriorAlgebra R M)) f * g).coeff n ∈ _
    rw [PowerSeries.coeff_mul]
    apply Submodule.sum_mem
    intro ij _
    rw [PowerSeries.coeff_map, ← Algebra.smul_def]
    exact (LinearMap.range (ι R)).smul_mem _ (hg ij.2)

theorem iotaSeries_mem_oddSeries (v : ℕ → M) : iotaSeries (R := R) v ∈ oddSeries :=
  fun n => ⟨v n, coeff_iotaSeries v n |>.symm⟩

theorem eq_iotaSeries_of_mem_oddSeries (f : PowerSeries (ExteriorAlgebra R M))
    (hf : f ∈ oddSeries) : ∃ v : ℕ → M, f = iotaSeries v := by
  choose v hv using hf
  refine ⟨v, ?_⟩
  ext n : 1
  simpa only [coeff_iotaSeries] using (hv n).symm

theorem sq_zero_of_mem_oddSeries [Algebra ℚ R]
    (f : PowerSeries (ExteriorAlgebra R M)) (hf : f ∈ oddSeries) : f * f = 0 := by
  obtain ⟨v, rfl⟩ := eq_iotaSeries_of_mem_oddSeries f hf
  exact iotaSeries_sq_zero v

variable {S I : Type*} [CommRing S] [Algebra ℚ R]

/-- Polynomial exterior substitution into series: coefficients are sent to
central scalar series, and every odd generator to an odd coefficient series. -/
def seriesLift (f : S →+* PowerSeries R) (v : I → ℕ → M) :
    ExteriorAlgebra S (I →₀ S) →+* PowerSeries (ExteriorAlgebra R M) := by
  let : Algebra S (PowerSeries (ExteriorAlgebra R M)) := Algebra.compHom _ f
  let g : (I →₀ S) →ₗ[S] PowerSeries (ExteriorAlgebra R M) :=
    Finsupp.linearCombination S (fun i => iotaSeries (v i))
  have hg (x : I →₀ S) : g x ∈ oddSeries := by
    induction x using Finsupp.induction with
    | zero => simp only [map_zero]; exact (oddSeries (R := R) (M := M)).zero_mem
    | @single_add i c x _ _ hx =>
      rw [map_add]
      apply (oddSeries (R := R) (M := M)).add_mem _ hx
      dsimp only [g]
      rw [Finsupp.linearCombination_single]
      change f c • iotaSeries (R := R) (v i) ∈ oddSeries (R := R) (M := M)
      exact (oddSeries (R := R) (M := M)).smul_mem _ (iotaSeries_mem_oddSeries (v i))
  exact (lift S ⟨g, fun x => sq_zero_of_mem_oddSeries (g x) (hg x)⟩).toRingHom

@[simp] theorem seriesLift_single (f : S →+* PowerSeries R) (v : I → ℕ → M) (i : I) :
    seriesLift f v (ι S (Finsupp.single i 1)) = iotaSeries (v i) := by
  simp [seriesLift]

@[simp] theorem seriesLift_algebraMap (f : S →+* PowerSeries R) (v : I → ℕ → M) (c : S) :
    seriesLift f v (algebraMap S (ExteriorAlgebra S (I →₀ S)) c) =
      PowerSeries.map (algebraMap R (ExteriorAlgebra R M)) (f c) := by
  simp [seriesLift, Algebra.compHom_algebraMap_apply]
  rfl

end ScalarSeries

end ExteriorAlgebra
