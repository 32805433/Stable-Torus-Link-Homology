import TorusLinkHomology.HilbertSeries.GradedDifferential
import TorusLinkHomology.HilbertSeries.QSeries.SpecializationAlgebra
import Mathlib.RingTheory.MvPowerSeries.Substitution

/-! Charge coordinates through the genuine substitution y ↦ s^N z.
The inverse reads coefficients on the support a ≥ Nh; no negative powers occur. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries

/-- Charge coordinates (k,b,h) become original degrees (k+Nh,b,h). -/
def chargeDegree (N : ℕ) (e : Fin 3 →₀ ℕ) : Fin 3 →₀ ℕ :=
  tridegree (e 0 + N * e 2) (e 1) (e 2)

theorem chargeDegree_injective (N : ℕ) : Function.Injective (chargeDegree N) := by
  intro e e' he
  have h0 := congrArg (fun d => d 0) he
  have h1 := congrArg (fun d => d 1) he
  have h2 := congrArg (fun d => d 2) he
  simp only [chargeDegree, tridegree_apply_zero, tridegree_apply_one, tridegree_apply_two] at h0 h1 h2
  ext i
  fin_cases i <;> simp_all

/-- Substitute the charge variable y by s^N z. -/
def chargeVariables (N : ℕ) : Fin 3 → Series :=
  ![MvPowerSeries.X 0, MvPowerSeries.X 1, MvPowerSeries.X 0 ^ N * MvPowerSeries.X 2]

theorem chargeVariables_hasSubst (N : ℕ) : MvPowerSeries.HasSubst (chargeVariables N) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [chargeVariables]

def chargeEmbedding (N : ℕ) : Series →ₐ[ℚ] Series :=
  MvPowerSeries.substAlgHom (chargeVariables_hasSubst N)

private theorem chargeVariables_prod (N : ℕ) (e : Fin 3 →₀ ℕ) :
    e.prod (fun i a => chargeVariables N i ^ a) =
      MvPowerSeries.monomial (chargeDegree N e) 1 := by
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, chargeVariables,
    Matrix.cons_val_zero]
  change (MvPowerSeries.X 0 : Series) ^ (e 0) *
    (MvPowerSeries.X 1 ^ (e 1) * ((MvPowerSeries.X 0 ^ N * MvPowerSeries.X 2) ^ (e 2))) = _
  rw [mul_pow, ← pow_mul]
  have he : (MvPowerSeries.X 0 : Series) ^ (e 0) *
      (MvPowerSeries.X 1 ^ (e 1) * (MvPowerSeries.X 0 ^ (N * e 2) * MvPowerSeries.X 2 ^ (e 2))) =
      MvPowerSeries.X 0 ^ (e 0 + N * e 2) * MvPowerSeries.X 1 ^ (e 1) * MvPowerSeries.X 2 ^ (e 2) := by
    rw [pow_add]
    ring
  rw [he]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, one_mul, chargeDegree, tridegree]

/-- The charge embedding preserves each coefficient at its reindexed degree. -/
theorem coeff_chargeEmbedding (N : ℕ) (f : Series) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff (chargeDegree N e) (chargeEmbedding N f) = MvPowerSeries.coeff e f := by
  rw [chargeEmbedding, MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.coeff_subst (chargeVariables_hasSubst N), finsum_eq_single _ e]
  · rw [chargeVariables_prod, MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    rw [chargeVariables_prod, MvPowerSeries.coeff_monomial_ne, smul_zero]
    exact fun he => hd ((chargeDegree_injective N) he.symm)

/-- Below the charge support cone every embedded coefficient vanishes. -/
theorem coeff_chargeEmbedding_eq_zero (N : ℕ) (f : Series) (e : Fin 3 →₀ ℕ)
    (he : e 0 < N * e 2) : MvPowerSeries.coeff e (chargeEmbedding N f) = 0 := by
  rw [chargeEmbedding, MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.coeff_subst (chargeVariables_hasSubst N)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rw [chargeVariables_prod, MvPowerSeries.coeff_monomial_ne, smul_zero]
  intro hd
  have h0 := congrArg (fun d => d 0) hd
  have h2 := congrArg (fun d => d 2) hd
  simp only [chargeDegree, tridegree_apply_zero, tridegree_apply_two] at h0 h2
  rw [h2] at he
  omega

theorem chargeEmbedding_injective (N : ℕ) : Function.Injective (chargeEmbedding N) := by
  intro f g he
  ext e
  simpa only [coeff_chargeEmbedding] using congrArg (MvPowerSeries.coeff (chargeDegree N e)) he

/-- Coefficientwise inverse of y ↦ s^N z on the charge support cone. -/
def chargeTransform (N : ℕ) (f : Series) : Series :=
  fun e => MvPowerSeries.coeff (chargeDegree N e) f

@[simp] theorem coeff_chargeTransform (N : ℕ) (f : Series) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (chargeTransform N f) = MvPowerSeries.coeff (chargeDegree N e) f := rfl

theorem chargeEmbedding_chargeTransform (N : ℕ) (f : Series)
    (hf : ∀ e, e 0 < N * e 2 → MvPowerSeries.coeff e f = 0) :
    chargeEmbedding N (chargeTransform N f) = f := by
  ext e
  by_cases he : N * e 2 ≤ e 0
  · have heq : chargeDegree N (tridegree (e 0 - N * e 2) (e 1) (e 2)) = e := by
      ext i
      fin_cases i <;> simp [chargeDegree, Nat.sub_add_cancel he]
    calc
      MvPowerSeries.coeff e (chargeEmbedding N (chargeTransform N f)) =
          MvPowerSeries.coeff (chargeDegree N (tridegree (e 0 - N * e 2) (e 1) (e 2)))
            (chargeEmbedding N (chargeTransform N f)) := by rw [heq]
      _ = MvPowerSeries.coeff (tridegree (e 0 - N * e 2) (e 1) (e 2))
            (chargeTransform N f) := coeff_chargeEmbedding _ _ _
      _ = MvPowerSeries.coeff e f := by
        rw [coeff_chargeTransform, heq]
  · rw [coeff_chargeEmbedding_eq_zero N _ e (by omega), hf e (by omega)]

theorem chargeTransform_chargeEmbedding (N : ℕ) (f : Series) :
    chargeTransform N (chargeEmbedding N f) = f := by
  ext e
  exact coeff_chargeEmbedding N f e

/-- The actual Hilbert series has a well-defined nonnegative charge expansion. -/
theorem chargeEmbedding_hilbertSeries (N n : ℕ) :
    chargeEmbedding N (chargeTransform N (hilbertSeries N n)) = hilbertSeries N n := by
  apply chargeEmbedding_chargeTransform
  intro e he
  change (homologyDimension N n (e 0) (e 1) (e 2) : ℚ) = 0
  rw [homologyDimension_eq_zero_of_exterior_bound he]
  rfl

end TorusLinkHomology.HilbertSeries
