import TorusLinkHomology.Generation.UniversalTransferNoV

/-! # Recovering the universal transfer identity from its comparison

The comparison is performed in the free polynomial exterior algebra. Its
no-v correction vanishes by uniqueness before any specialization is made.
-/

noncomputable section

namespace TorusLinkHomology.UniversalTransfer

/-- The coefficientwise conclusion of the closed comparison construction.
The hypotheses isolate the differential identity and the Q=0 evaluation;
the conclusion is an equality of chains, not just of homology classes. -/
theorem transfer_identity_of_comparison (N m q : ℕ) (hN : 0 < N) (hm : 0 < m)
    (t : Fin (q + 1) → ℕ) (htN : ∀ i, t i < N) (htm : ∀ i, t i < m)
    (c : ℚ) (P S B : A)
    (hB : d N m B = c • (v 0 • orderedA (q + 1) t) - S)
    (hP : d N m P = 0) (hPv : NoV P) (hSv : NoV S)
    (hPQ : eraseQ P = ((-1 : ℚ) ^ (q + 1)) • S) (hSQ : eraseQ S = S) :
    c • omega N m q t = d N m B + ((-1 : ℚ) ^ (q + 1)) • P := by
  let R : A := ((-1 : ℚ) ^ (q + 1)) • P - S -
    c • (etaPrime N m * betaDeletion N q t)
  have hR : NoV R :=
    ((hPv.rat_smul _).sub hSv).sub ((noV_etaPrime_mul_betaDeletion N m q t).rat_smul c)
  have hrewrite : R = d N m B + ((-1 : ℚ) ^ (q + 1)) • P - c • omega N m q t := by
    rw [hB, omega]
    dsimp only [R]
    rw [smul_add]
    abel
  have hdR : d N m R = 0 := by
    rw [hrewrite, map_sub, map_add, d_squared, map_rat_smul, hP, smul_zero,
      map_rat_smul, omega_is_cycle N m q hN hm t htN htm, smul_zero]
    simp
  have hsign : ((-1 : ℚ) ^ (q + 1)) * ((-1 : ℚ) ^ (q + 1)) = 1 := by
    rw [← mul_pow]
    norm_num
  have hQR : eraseQ R = 0 := by
    dsimp only [R]
    rw [map_sub, map_sub, map_rat_smul, hPQ, hSQ, smul_smul, hsign, one_smul,
      sub_self, map_rat_smul, map_mul, eraseQ_etaPrime, zero_mul, smul_zero, sub_self]
  have hzero : R = 0 := noV_cycle_eq_zero N m hN hm R hR hdR hQR
  rw [hrewrite] at hzero
  exact (sub_eq_zero.mp hzero).symm

end TorusLinkHomology.UniversalTransfer
