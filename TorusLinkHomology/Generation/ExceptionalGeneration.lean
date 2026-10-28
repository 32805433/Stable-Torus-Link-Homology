import TorusLinkHomology.Generation.ComparisonGeneration
import TorusLinkHomology.Generation.ComparisonExplicit

/-!
# Reduction to ordered squarefree exceptional products

The exceptional family is the image of a finite free exterior algebra.
Its standard basis is indexed by finite sets, so basis expansion implements
both the reordering signs and the vanishing of repeated odd factors.
-/

noncomputable section

open scoped BigOperators

namespace ExteriorAlgebra

variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]

/-- Move an arbitrary exterior element across one odd vector. -/
theorem mul_iota_eq_iota_mul_involute (x : ExteriorAlgebra S M) (v : M) :
    x * ι S v = ι S v * CliffordAlgebra.involute x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => rw [AlgHom.commutes, Algebra.commutes]
  | add x y hx hy => simp only [add_mul, map_add, mul_add, hx, hy]
  | ι_mul x w hx =>
    rw [mul_assoc, hx, ← mul_assoc]
    have hswap : ι S w * ι S v = -(ι S v * ι S w) :=
      eq_neg_of_add_eq_zero_left (ι_add_mul_swap w v)
    rw [hswap, map_mul, CliffordAlgebra.involute_ι]
    simp only [neg_mul, mul_neg, mul_assoc]

/-- Moving past an ordered exterior product applies the grade involution
once for each factor. -/
theorem mul_iotaMulti_eq (q : ℕ) (x : ExteriorAlgebra S M) (v : Fin q → M) :
    x * ιMulti S q v =
      ιMulti S q v * (CliffordAlgebra.involute^[q]) x := by
  induction q generalizing x with
  | zero => simp [ιMulti_zero_apply]
  | succ q ih =>
    rw [ιMulti_succ_apply, ← mul_assoc, mul_iota_eq_iota_mul_involute,
      mul_assoc, ih, ← mul_assoc, Function.iterate_succ_apply]

end ExteriorAlgebra

namespace TorusLinkHomology.CoefficientComplex

/-- The number of exceptional indices at the new offset. -/
def exceptionalCount (N r ell : ℕ) : ℕ := min N (N * (r + 1) - (ell + 1))

abbrev ExceptionalVectors (N r ell : ℕ) := Fin (exceptionalCount N r ell) →₀ R r

abbrev ExceptionalExterior (N r ell : ℕ) :=
  ExteriorAlgebra (R r) (ExceptionalVectors N r ell)

/-- The finite exceptional family, realized as degree-one vectors. -/
def exceptionalVectorMap (N r ell : ℕ) : ExceptionalVectors N r ell →ₗ[R r] V r :=
  Finsupp.linearCombination (R r)
    (fun i => tailVector N r (ell + 1) (N * (r + 1) - i.val))

def exceptionalMap (N r ell : ℕ) : ExceptionalExterior N r ell →ₐ[R r] A r :=
  ExteriorAlgebra.map (exceptionalVectorMap N r ell)

/-- The canonical ordered, squarefree exceptional product indexed by `s`. -/
def exceptionalProduct (N r ell : ℕ) (s : Finset (Fin (exceptionalCount N r ell))) : A r :=
  exceptionalMap N r ell
    ((Finsupp.basisSingleOne : Module.Basis (Fin (exceptionalCount N r ell))
      (R r) (ExceptionalVectors N r ell)).ExteriorAlgebra s)

@[simp] theorem exceptionalMap_iota_single (N r ell : ℕ)
    (i : Fin (exceptionalCount N r ell)) :
    exceptionalMap N r ell (ExteriorAlgebra.ι (R r) (Finsupp.single i 1)) =
      tail N r (ell + 1) (N * (r + 1) - i.val) := by
  simp [exceptionalMap, exceptionalVectorMap]

/-- The finite-set basis convention is the increasing order of deficits. -/
theorem exceptionalProduct_eq_iotaMulti (N r ell : ℕ)
    (s : Finset (Fin (exceptionalCount N r ell))) :
    exceptionalProduct N r ell s =
      ExteriorAlgebra.ιMulti (R r) s.card
        (fun j => tailVector N r (ell + 1)
          (N * (r + 1) - (s.orderEmbOfFin rfl j).val)) := by
  rw [exceptionalProduct, exceptionalMap, ExteriorAlgebra.basis_apply]
  unfold ExteriorAlgebra.ιMulti_family
  rw [ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext j
  simp [exceptionalVectorMap, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Set.powersetCard.prodEquiv_symm_apply, Set.powersetCard.ofCard]

theorem mul_exceptionalProduct (N r ell : ℕ)
    (s : Finset (Fin (exceptionalCount N r ell))) (x : A r) :
    x * exceptionalProduct N r ell s =
      exceptionalProduct N r ell s * (CliffordAlgebra.involute^[s.card]) x := by
  unfold exceptionalProduct exceptionalMap
  rw [ExteriorAlgebra.basis_apply]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.map_apply_ιMulti]
  exact ExteriorAlgebra.mul_iotaMulti_eq _ _ _

theorem involute_tail (N r ell j : ℕ) :
    CliffordAlgebra.involute (tail N r ell j) = -tail N r ell j := by
  rw [← iota_tailVector, CliffordAlgebra.involute_ι]

theorem involute_mem_tailSubalgebra (N r ell : ℕ) (b : A r)
    (hb : b ∈ tailSubalgebra N r ell) :
    CliffordAlgebra.involute b ∈ tailSubalgebra N r ell := by
  induction hb using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨j, hj, hNr, rfl⟩ := hb
    rw [involute_tail]
    exact (tailSubalgebra N r ell).neg_mem (tail_mem_tailSubalgebra _ _ _ _ hj hNr)
  | algebraMap c => rw [AlgHom.commutes]; exact (tailSubalgebra N r ell).algebraMap_mem c
  | add x y _ _ hx hy => rw [map_add]; exact (tailSubalgebra N r ell).add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact (tailSubalgebra N r ell).mul_mem hx hy

theorem involute_iterate_mem_tailSubalgebra (N r ell q : ℕ) (b : A r)
    (hb : b ∈ tailSubalgebra N r ell) :
    (CliffordAlgebra.involute^[q]) b ∈ tailSubalgebra N r ell := by
  induction q with
  | zero => exact hb
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact involute_mem_tailSubalgebra N r ell _ ih

theorem rhoSucc_involute (N r ell : ℕ) (b : A (r + 1)) :
    rhoSucc N r ell (CliffordAlgebra.involute b) =
      CliffordAlgebra.involute (rhoSucc N r ell b) := by
  induction b using CliffordAlgebra.left_induction with
  | algebraMap c => rw [AlgHom.commutes, rhoSucc_algebraMap, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    simp only [map_mul, CliffordAlgebra.involute_ι, map_neg, hx]
    congr 1
    change -(ExteriorAlgebra.mapOfSemilinear _ _ _) =
      CliffordAlgebra.involute (ExteriorAlgebra.mapOfSemilinear _ _ _)
    rw [ExteriorAlgebra.mapOfSemilinear_iota, CliffordAlgebra.involute_ι]

theorem rhoSucc_involute_iterate (N r ell q : ℕ) (b : A (r + 1)) :
    rhoSucc N r ell ((CliffordAlgebra.involute^[q]) b) =
      (CliffordAlgebra.involute^[q]) (rhoSucc N r ell b) := by
  induction q with
  | zero => rfl
  | succ q ih => rw [Function.iterate_succ_apply', rhoSucc_involute, ih, Function.iterate_succ_apply']

/-- Normal expressions with every exceptional factor on the left and every
liftable factor on the right. -/
def exceptionalNormalSpan (N r ell : ℕ) : Submodule (R r) (A r) :=
  Submodule.span (R r) {a | ∃ s : Finset (Fin (exceptionalCount N r ell)),
    ∃ b : A (r + 1), b ∈ tailSubalgebra N (r + 1) (ell + 1) ∧
      a = exceptionalProduct N r ell s * rhoSucc N r (ell + 1) b}

theorem exceptionalProduct_mul_mem_normalSpan (N r ell : ℕ)
    (s : Finset (Fin (exceptionalCount N r ell))) (b : A (r + 1))
    (hb : b ∈ tailSubalgebra N (r + 1) (ell + 1)) :
    exceptionalProduct N r ell s * rhoSucc N r (ell + 1) b ∈ exceptionalNormalSpan N r ell :=
  Submodule.subset_span ⟨s, b, hb, rfl⟩

/-- Basis expansion in the finite exterior algebra is the squarefree
straightening step; coefficients stay in the original polynomial ring. -/
theorem exceptionalMap_mul_mem_normalSpan (N r ell : ℕ) (x : ExceptionalExterior N r ell)
    (b : A (r + 1)) (hb : b ∈ tailSubalgebra N (r + 1) (ell + 1)) :
    exceptionalMap N r ell x * rhoSucc N r (ell + 1) b ∈ exceptionalNormalSpan N r ell := by
  let B := (Finsupp.basisSingleOne : Module.Basis (Fin (exceptionalCount N r ell))
    (R r) (ExceptionalVectors N r ell)).ExteriorAlgebra
  rw [← B.sum_repr x, map_sum, Finset.sum_mul]
  apply Submodule.sum_mem
  intro s _
  rw [map_smul, smul_mul_assoc]
  exact (exceptionalNormalSpan N r ell).smul_mem _
    (exceptionalProduct_mul_mem_normalSpan N r ell s b hb)

theorem exceptional_mul_mem_normalSpan (N r ell : ℕ)
    (i : Fin (exceptionalCount N r ell)) (a : A r)
    (ha : a ∈ exceptionalNormalSpan N r ell) :
    tail N r (ell + 1) (N * (r + 1) - i.val) * a ∈ exceptionalNormalSpan N r ell := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, b, hb, rfl⟩ := ha
    rw [← exceptionalMap_iota_single N r ell i, ← mul_assoc]
    unfold exceptionalProduct
    rw [← map_mul]
    exact exceptionalMap_mul_mem_normalSpan N r ell _ b hb
  | zero => simpa only [mul_zero] using (exceptionalNormalSpan N r ell).zero_mem
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact (exceptionalNormalSpan N r ell).add_mem hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact (exceptionalNormalSpan N r ell).smul_mem c hx

theorem reduced_mul_mem_normalSpan (N r ell : ℕ) (b : A (r + 1))
    (hb : b ∈ tailSubalgebra N (r + 1) (ell + 1)) (a : A r)
    (ha : a ∈ exceptionalNormalSpan N r ell) :
    rhoSucc N r (ell + 1) b * a ∈ exceptionalNormalSpan N r ell := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨s, c, hc, rfl⟩ := ha
    rw [← mul_assoc, mul_exceptionalProduct, mul_assoc, ← rhoSucc_involute_iterate, ← map_mul]
    apply exceptionalProduct_mul_mem_normalSpan
    exact (tailSubalgebra N (r + 1) (ell + 1)).mul_mem
      (involute_iterate_mem_tailSubalgebra N (r + 1) (ell + 1) s.card b hb) hc
  | zero => simpa only [mul_zero] using (exceptionalNormalSpan N r ell).zero_mem
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact (exceptionalNormalSpan N r ell).add_mem hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact (exceptionalNormalSpan N r ell).smul_mem c hx

/-- The normal span is stable under left multiplication by every old tail
expression; adjoin induction requires no assumption of module generation. -/
theorem old_mul_mem_normalSpan (N r ell : ℕ) (hm : ell + 1 ≤ N * (r + 1))
    (a : A r) (ha : a ∈ tailSubalgebra N r (ell + 1)) :
    ∀ x ∈ exceptionalNormalSpan N r ell, a * x ∈ exceptionalNormalSpan N r ell := by
  rw [old_tailSubalgebra_eq_adjoin N r (ell + 1) hm] at ha
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    rcases ha with ha | ha
    · obtain ⟨t, ht, rfl⟩ := ha
      exact exceptional_mul_mem_normalSpan N r ell ⟨t, ht⟩
    · obtain ⟨b, hb, rfl⟩ := ha
      exact reduced_mul_mem_normalSpan N r ell b hb
  | algebraMap c =>
    intro x hx
    rw [← Algebra.smul_def]
    exact (exceptionalNormalSpan N r ell).smul_mem c hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [add_mul]
    exact (exceptionalNormalSpan N r ell).add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [mul_assoc]
    exact ha _ (hb x hx)

/-- Every old tail expression is an actual polynomial-coefficient linear
combination of squarefree exceptional products times reduced new tails. -/
theorem old_mem_normalSpan (N r ell : ℕ) (hm : ell + 1 ≤ N * (r + 1))
    (a : A r) (ha : a ∈ tailSubalgebra N r (ell + 1)) :
    a ∈ exceptionalNormalSpan N r ell := by
  have h1 : (1 : A r) ∈ exceptionalNormalSpan N r ell := by
    simpa only [map_one, mul_one] using exceptionalMap_mul_mem_normalSpan N r ell 1 1
      (tailSubalgebra N (r + 1) (ell + 1)).one_mem
  simpa only [mul_one] using old_mul_mem_normalSpan N r ell hm a ha 1 h1

@[simp] theorem exceptionalProduct_empty (N r ell : ℕ) :
    exceptionalProduct N r ell ∅ = 1 := by
  unfold exceptionalProduct
  rw [ExteriorAlgebra.basis_apply_ofCard _ (show (∅ : Finset (Fin (exceptionalCount N r ell))).card = 0 from rfl)]
  unfold ExteriorAlgebra.ιMulti_family
  rw [ExteriorAlgebra.ιMulti_apply]
  simp

theorem exceptionalMap_mem_tailSubalgebra (N r ell : ℕ)
    (hm : ell + 1 ≤ N * (r + 1)) (a : ExceptionalExterior N r ell) :
    exceptionalMap N r ell a ∈ tailSubalgebra N r (ell + 1) := by
  have hsingle (i : Fin (exceptionalCount N r ell)) :
      exceptionalMap N r ell (ExteriorAlgebra.ι (R r) (Finsupp.single i 1)) ∈
        tailSubalgebra N r (ell + 1) := by
    rw [exceptionalMap_iota_single]
    have hthreshold := exceptional_threshold N r (ell + 1) hm
    have hi : i.val < min N (N * (r + 1) - (ell + 1)) := i.isLt
    exact tail_mem_tailSubalgebra _ _ _ _ (by omega) (by omega)
  induction a using ExteriorAlgebra.induction with
  | algebraMap c => rw [AlgHom.commutes]; exact (tailSubalgebra N r (ell + 1)).algebraMap_mem c
  | ι m =>
    have hm : (∑ i : Fin (exceptionalCount N r ell), m i • Finsupp.single i (1 : R r)) = m :=
      (Finsupp.basisSingleOne : Module.Basis (Fin (exceptionalCount N r ell))
        (R r) (ExceptionalVectors N r ell)).sum_repr m
    rw [← hm, map_sum, map_sum]
    apply Subalgebra.sum_mem
    intro i _
    rw [map_smul, map_smul]
    exact (tailSubalgebra N r (ell + 1)).smul_mem (hsingle i) _
  | add x y hx hy => rw [map_add]; exact (tailSubalgebra N r (ell + 1)).add_mem hx hy
  | mul x y hx hy => rw [map_mul]; exact (tailSubalgebra N r (ell + 1)).mul_mem hx hy

theorem exceptionalProduct_is_cycle (N r ell : ℕ)
    (hm : ell + 1 ≤ N * (r + 1)) (s : Finset (Fin (exceptionalCount N r ell))) :
    d N r (ell + 1) (exceptionalProduct N r ell s) = 0 :=
  tailSubalgebra_le_cycles N r (ell + 1) (exceptionalMap_mem_tailSubalgebra N r ell hm _)

/-- Chains admitting a tail representative modulo an explicit boundary. -/
def tailRepresentativeSpace (N r ell : ℕ) : Submodule (R r) (A r) where
  carrier := {z | ∃ s, s ∈ tailSubalgebra N r ell ∧ ∃ b, z = s + d N r ell b}
  zero_mem' := ⟨0, (tailSubalgebra N r ell).zero_mem, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, b, rfl⟩ ⟨t, ht, c, rfl⟩
    refine ⟨s + t, (tailSubalgebra N r ell).add_mem hs ht, b + c, ?_⟩
    rw [map_add]
    abel
  smul_mem' := by
    rintro c x ⟨s, hs, b, rfl⟩
    exact ⟨c • s, (tailSubalgebra N r ell).smul_mem hs c, c • b, by rw [smul_add, map_smul]⟩

theorem tailRepresentativeSpace_mul_tail (N r ell : ℕ) (z b : A r)
    (hz : z ∈ tailRepresentativeSpace N r ell) (hb : b ∈ tailSubalgebra N r ell) :
    z * b ∈ tailRepresentativeSpace N r ell := by
  obtain ⟨s, hs, c, rfl⟩ := hz
  refine ⟨s * b, (tailSubalgebra N r ell).mul_mem hs hb, c * b, ?_⟩
  have hcycle : d N r ell b = 0 := tailSubalgebra_le_cycles N r ell hb
  rw [(dga N r ell).d_mul_of_cycle hcycle, add_mul]

theorem ConnectingRepresentative.add {N r ell : ℕ} {a b : A r} {z t : A (r + 1)}
    (hz : ConnectingRepresentative N r ell a z)
    (ht : ConnectingRepresentative N r ell b t) :
    ConnectingRepresentative N r ell (a + b) (z + t) := by
  obtain ⟨w, hw, hzw⟩ := hz
  obtain ⟨v, hv, htv⟩ := ht
  exact ⟨w + v, by rw [p_add, hw, hv], by rw [map_add, map_add, hzw, htv]⟩

theorem ConnectingRepresentative.smul {N r ell : ℕ} {a : A r} {z : A (r + 1)}
    (hz : ConnectingRepresentative N r ell a z) (c : R (r + 1)) :
    ConnectingRepresentative N r ell (reduceCoefficients r c • a) (c • z) := by
  obtain ⟨w, hw, hzw⟩ := hz
  exact ⟨c • w, by rw [p_smul, hw], by rw [map_smul, map_smul, hzw]⟩

/-- Source chains whose connecting class has at least one tail representative.
Coefficient scalars are lifted through the explicit polynomial section. -/
def connectingTailSources (N r ell : ℕ) : Submodule (R r) (A r) where
  carrier := {a | ∃ z, ConnectingRepresentative N r ell a z ∧
    z ∈ tailRepresentativeSpace N (r + 1) (ell + 1)}
  zero_mem' := ⟨0, ⟨0, by simp [p], by simp⟩, (tailRepresentativeSpace N (r + 1) (ell + 1)).zero_mem⟩
  add_mem' := by
    rintro a b ⟨z, hz, hzt⟩ ⟨t, ht, htt⟩
    exact ⟨z + t, hz.add ht, (tailRepresentativeSpace N (r + 1) (ell + 1)).add_mem hzt htt⟩
  smul_mem' := by
    rintro c a ⟨z, hz, hzt⟩
    refine ⟨includeCoefficients r c • z, ?_,
      (tailRepresentativeSpace N (r + 1) (ell + 1)).smul_mem _ hzt⟩
    simpa only [reduceCoefficients_include] using hz.smul (includeCoefficients r c)

/-- The finite hypothesis required by the induction: connecting classes of
nonempty ordered squarefree exceptional products have tail representatives. -/
def ExceptionalTransfers (N r ell : ℕ) : Prop :=
  ∀ s : Finset (Fin (exceptionalCount N r ell)), s.Nonempty →
    ∀ z : A (r + 1), ConnectingRepresentative N r ell (exceptionalProduct N r ell s) z →
      z ∈ tailRepresentativeSpace N (r + 1) (ell + 1)

/-- A single explicit representative for each finite exceptional product
suffices; independence of the lift supplies every other representative. -/
theorem exceptionalTransfers_of_representatives (N r ell : ℕ)
    (hm : ell + 1 < N * (r + 1))
    (h : ∀ s : Finset (Fin (exceptionalCount N r ell)), s.Nonempty →
      ∃ z : A (r + 1), ConnectingRepresentative N r ell (exceptionalProduct N r ell s) z ∧
        z ∈ tailRepresentativeSpace N (r + 1) (ell + 1)) :
    ExceptionalTransfers N r ell := by
  intro s hs z hz
  obtain ⟨z₀, hz₀, hgood⟩ := h s hs
  obtain ⟨c, hc⟩ := hz.eq_mod_boundary hm hz₀
  rw [hc]
  apply (tailRepresentativeSpace N (r + 1) (ell + 1)).add_mem hgood
  exact ⟨0, (tailSubalgebra N (r + 1) (ell + 1)).zero_mem, c, by simp⟩

theorem exceptionalProduct_mem_connectingTailSources (N r ell : ℕ)
    (hm : ell + 1 < N * (r + 1)) (htransfers : ExceptionalTransfers N r ell)
    (s : Finset (Fin (exceptionalCount N r ell))) :
    exceptionalProduct N r ell s ∈ connectingTailSources N r ell := by
  by_cases hs : s.Nonempty
  · obtain ⟨z, hz⟩ := connectingRepresentative_exists N r ell hm _
      (exceptionalProduct_is_cycle N r ell (Nat.le_of_lt hm) s)
    exact ⟨z, hz, htransfers s hs z hz⟩
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hs0, exceptionalProduct_empty]
    refine ⟨algebraMap (R (r + 1)) (A (r + 1)) (G N (r + 1) (ell + 1)),
      connecting_empty_product N r ell, ?_⟩
    exact ⟨algebraMap (R (r + 1)) (A (r + 1)) (G N (r + 1) (ell + 1)),
      (tailSubalgebra N (r + 1) (ell + 1)).algebraMap_mem _, 0, by simp⟩

theorem normalSpan_le_connectingTailSources (N r ell : ℕ)
    (hm : ell + 1 < N * (r + 1)) (htransfers : ExceptionalTransfers N r ell) :
    exceptionalNormalSpan N r ell ≤ connectingTailSources N r ell := by
  apply Submodule.span_le.mpr
  rintro a ⟨s, b, hb, rfl⟩
  obtain ⟨z, hz, hzt⟩ := exceptionalProduct_mem_connectingTailSources N r ell hm htransfers s
  refine ⟨z * b, hz.mul_cycle (tailSubalgebra_le_cycles N (r + 1) (ell + 1) hb), ?_⟩
  exact tailRepresentativeSpace_mul_tail N (r + 1) (ell + 1) z b hzt hb

/-- CI-16: old generation and the finite transfer hypotheses control every
connecting representative, with its boundary witness retained. -/
theorem connecting_mem_tailRepresentativeSpace (N r ell : ℕ)
    (hm : ell + 1 < N * (r + 1))
    (hold : TailGeneration N r (ell + 1)) (htransfers : ExceptionalTransfers N r ell)
    (a : A r) (ha : d N r (ell + 1) a = 0) (z : A (r + 1))
    (hz : ConnectingRepresentative N r ell a z) :
    z ∈ tailRepresentativeSpace N (r + 1) (ell + 1) := by
  obtain ⟨a₀, ha₀, q, hq⟩ := hold a ha
  have ha₀normal := old_mem_normalSpan N r ell (Nat.le_of_lt hm) a₀ ha₀
  obtain ⟨z₀, hz₀, s, hs, b, hb⟩ :=
    normalSpan_le_connectingTailSources N r ell hm htransfers ha₀normal
  have hdiff := hz.sub hz₀
  have hsource : a - a₀ = d N r (ell + 1) q := by rw [hq, add_sub_cancel_left]
  rw [hsource] at hdiff
  obtain ⟨c, hc⟩ := hdiff.boundary_of_source_boundary hm
  refine ⟨s, hs, b + c, ?_⟩
  rw [map_add, ← hc]
  rw [hb]
  abel

/-- CI-15/16: the two neighboring generation statements and the finite set of
exceptional-product transfers imply generation in the new complex. -/
theorem tailGeneration_of_exceptionalTransfers (N r ell : ℕ)
    (hm : ell + 1 < N * (r + 1))
    (hmiddle : TailGeneration N (r + 1) ell)
    (hold : TailGeneration N r (ell + 1))
    (htransfers : ExceptionalTransfers N r ell) :
    TailGeneration N (r + 1) (ell + 1) := by
  apply tailGeneration_of_connecting N r ell hm hmiddle
  exact connecting_mem_tailRepresentativeSpace N r ell hm hold htransfers

end TorusLinkHomology.CoefficientComplex
