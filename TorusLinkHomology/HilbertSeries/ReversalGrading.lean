import TorusLinkHomology.HilbertSeries.ReversalHomology

/-! Weights of the passive-monomial homology decomposition. -/
noncomputable section
set_option maxRecDepth 4000
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries.GeneralReversal
open CoordinateKoszul

/-- Auxiliary weight carried by an active original monomial. -/
def activeWeight (N r : ℕ) {m : ℕ} (q : ChainIndex m) : ℕ :=
  (∑ i : Fin m, (r - i.val) * q.1 i) + ∑ i ∈ q.2, (N * r - i.val)

/-- Passive polynomial indices have weights 1,...,p; passive exterior indices
have weights Nr+1,...,Nr+p. -/
def passiveWeight (N m p : ℕ) (t : ChainIndex p) : ℕ :=
  (∑ i : Fin p, (i.val + 1) * t.1 i) + ∑ i ∈ t.2, (N * (m + p) + i.val + 1)

theorem activeWeight_add_weight (N m r : ℕ) (hN : 0 < N) (hmr : m ≤ r)
    (q : ChainIndex m) :
    activeWeight N r q + (monomialDegree N q).2.1 = r * (monomialDegree N q).1 := by
  have hrNr : r ≤ N * r := by simpa using Nat.mul_le_mul_right r hN
  have hp : (∑ i : Fin m, (r - i.val) * q.1 i) +
      (∑ i : Fin m, i.val * q.1 i) = r * ∑ i : Fin m, q.1 i := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  have he : (∑ i ∈ q.2, (N * r - i.val)) + (∑ i ∈ q.2, i.val) = N * r * q.2.card := by
    rw [← Finset.sum_add_distrib]
    have hs : ∀ i ∈ q.2, N * r - i.val + i.val = N * r := by
      intro i hi
      rw [Nat.sub_add_cancel (by omega)]
    simp only [Finset.sum_congr rfl hs, Finset.sum_const, smul_eq_mul]
    exact Nat.mul_comm _ _
  unfold activeWeight monomialDegree
  dsimp only
  nlinarith

private theorem pow_mem_auxiliary {ell r w h : ℕ} {x : A r}
    (hx : x ∈ Auxiliary.chainPiece ell r w h) (k : ℕ) :
    x ^ k ∈ Auxiliary.chainPiece ell r (k * w) (k * h) := by
  induction k with
  | zero => simpa using Auxiliary.one_mem_chainPiece ell r
  | succ k ih =>
    simpa only [pow_succ, Nat.succ_mul] using Auxiliary.mul_mem_chainPiece ih hx

private theorem active_polynomial_mem (N m r : ℕ) (hmr : m ≤ r) (q : Fin m →₀ ℕ) :
    activeChains m r hmr (algebraMap (R m) (A m) (MvPolynomial.monomial q 1)) ∈
      Auxiliary.chainPiece (N * r - m) r (∑ i : Fin m, (r - i.val) * q i) 0 := by
  classical
  induction q using Finsupp.induction with
  | zero => simpa using Auxiliary.one_mem_chainPiece (N * r - m) r
  | single_add i k q hi hk ih =>
    have hp : MvPolynomial.monomial (Finsupp.single i k + q) (1 : ℚ) =
        u m i ^ k * MvPolynomial.monomial q 1 := by
      rw [u, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
    rw [hp, map_mul, map_mul, map_pow, map_pow]
    have hpow := pow_mem_auxiliary (activeChains_u_mem N m r hmr i) k
    have hmul := Auxiliary.mul_mem_chainPiece hpow ih
    convert hmul using 1
    · simp only [Finsupp.add_apply, Nat.mul_add, Finset.sum_add_distrib]
      simp [Finsupp.single_apply, Nat.mul_comm]

private theorem active_exterior_list_mem (N m r : ℕ) (hN : 0 < N) (hmr : m ≤ r)
    (l : List (Fin m)) :
    activeChains m r hmr ((l.map (xi m)).prod) ∈
      Auxiliary.chainPiece (N * r - m) r ((l.map fun i => N * r - i.val).sum) l.length := by
  induction l with
  | nil => simpa using Auxiliary.one_mem_chainPiece (N * r - m) r
  | cons i l ih =>
    simpa only [List.map_cons, List.prod_cons, map_mul, List.sum_cons, List.length_cons,
      Nat.add_comm 1] using Auxiliary.mul_mem_chainPiece
      (activeChains_xi_mem N m r hN hmr i) ih

theorem activeChains_basis_mem (N m r : ℕ) (hN : 0 < N) (hmr : m ≤ r) (q : ChainIndex m) :
    activeChains m r hmr (rationalChainBasis m q) ∈
      Auxiliary.chainPiece (N * r - m) r (activeWeight N r q) q.2.card := by
  classical
  have he := active_exterior_list_mem N m r hN hmr q.2.sort
  rw [← chainBasis_eq_sort_prod] at he
  rw [← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset] at he
  simp only [Finset.length_sort] at he
  have hp := active_polynomial_mem N m r hmr q.1
  have hm := Auxiliary.mul_mem_chainPiece hp he
  simpa only [rationalChainBasis_apply, Algebra.smul_def, map_mul, Nat.zero_add,
    activeWeight] using hm

/-- The active embedding specializes the original grading by w = r*a-b. -/
theorem activeChains_mem (N m r a b h w : ℕ) (hN : 0 < N) (hmr : m ≤ r)
    (hw : w + b = r * a) {x : A m} (hx : x ∈ chainPiece N m a b h) :
    activeChains m r hmr x ∈ Auxiliary.chainPiece (N * r - m) r w h := by
  rw [chainPiece_eq_span_degree] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, hq, rfl⟩ := hx
    have hwq := activeWeight_add_weight N m r hN hmr q
    have hdeg : monomialDegree N q = (a, b, h) := hq
    have he : activeWeight N r q = w := by simp only [hdeg] at hwq; omega
    have hh : q.2.card = h := congrArg (fun t => t.2.2) hdeg
    simpa only [he, hh] using activeChains_basis_mem N m r hN hmr q
  | zero => simp
  | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_rat_smul] using Submodule.smul_mem _ c ih

private theorem lowPolynomialIndex_weight (m p : ℕ) (q : Fin p →₀ ℕ) :
    (∑ i : Fin (m + p), (i.val + 1) * q.mapDomain (lowPolynomialIndex m p) i) =
      ∑ i : Fin p, (i.val + 1) * q i := by
  rw [← Finsupp.sum_fintype _ (fun (i : Fin (m + p)) (n : ℕ) => (i.val + 1) * n) (by simp),
    Finsupp.sum_mapDomain_index_inj (lowPolynomialIndex m p).injective,
    Finsupp.sum_fintype _ _ (by simp)]
  rfl

theorem passiveMonomial_mem (N m p : ℕ) (hN : 0 < N) (t : ChainIndex p) :
    passiveMonomial m p t ∈
      Auxiliary.chainPiece (N * (m + p) - m) (m + p) (passiveWeight N m p t) t.2.card := by
  classical
  have hr : m ≤ N * (m + p) := (Nat.le_add_right m p).trans
    (by simpa using Nat.mul_le_mul_right (m + p) hN)
  have he : passiveMonomial m p t =
      rationalChainBasis (m + p)
        (t.1.mapDomain (lowPolynomialIndex m p), t.2.map (Fin.natAddEmb m)) := by
    rw [rationalChainBasis_apply]
    change MvPolynomial.rename (lowPolynomialIndex m p) (MvPolynomial.monomial t.1 1) • _ = _
    rw [MvPolynomial.rename_monomial]
  rw [he]
  have hm := Auxiliary.rationalChainBasis_mem (N * (m + p) - m) (m + p)
    (t.1.mapDomain (lowPolynomialIndex m p), t.2.map (Fin.natAddEmb m))
  simpa only [Auxiliary.monomialDegree, lowPolynomialIndex_weight, Finset.sum_map,
    Fin.natAddEmb_apply, Fin.val_natAdd, Finset.card_map,
    show ∀ i : Fin p, N * (m + p) - m + (m + i.val) + 1 = N * (m + p) + i.val + 1
      from fun i => by omega, passiveWeight] using hm

/-- A basis indexed by passive monomials and original active monomials. -/
def decompositionBasis (m p : ℕ) :
    Module.Basis (Σ _ : ChainIndex p, ChainIndex m) ℚ (A (m + p)) :=
  (Finsupp.basis (fun _ : ChainIndex p => rationalChainBasis m)).map (decomposeChains m p).symm

@[simp] theorem decompositionBasis_apply (m p : ℕ) (t : ChainIndex p) (q : ChainIndex m) :
    decompositionBasis m p ⟨t, q⟩ =
      activeChains m (m + p) (Nat.le_add_right m p) (rationalChainBasis m q) *
        passiveMonomial m p t := by
  simp only [decompositionBasis, Module.Basis.map_apply, Finsupp.coe_basis,
    decomposeChains_symm_single]

theorem decompositionBasis_mem (N m p : ℕ) (hN : 0 < N)
    (t : ChainIndex p) (q : ChainIndex m) :
    decompositionBasis m p ⟨t, q⟩ ∈
      Auxiliary.chainPiece (N * (m + p) - m) (m + p)
        (activeWeight N (m + p) q + passiveWeight N m p t) (q.2.card + t.2.card) := by
  rw [decompositionBasis_apply]
  exact Auxiliary.mul_mem_chainPiece
    (activeChains_basis_mem N m (m + p) hN (Nat.le_add_right m p) q)
    (passiveMonomial_mem N m p hN t)

@[simp] theorem decomposeChains_decompositionBasis (m p : ℕ) (t : ChainIndex p) (q : ChainIndex m) :
    decomposeChains m p (decompositionBasis m p ⟨t, q⟩) =
      Finsupp.single t (rationalChainBasis m q) := by
  simp only [decompositionBasis, Module.Basis.map_apply, Finsupp.coe_basis,
    LinearEquiv.apply_symm_apply]

/-- Degree of the basis associated with passive and original active monomials. -/
def decompositionDegree (N m p : ℕ) (i : Σ _ : ChainIndex p, ChainIndex m) : ℕ × ℕ :=
  (activeWeight N (m + p) i.2 + passiveWeight N m p i.1, i.2.2.card + i.1.2.card)

theorem auxiliaryProjection_eq_diagonal (N m p w h : ℕ) (hN : 0 < N) :
    Auxiliary.homogeneousProjection (N * (m + p) - m) (m + p) w h =
      (decompositionBasis m p).rationalDiagonal
        (fun i => if decompositionDegree N m p i = (w, h) then 1 else 0) := by
  classical
  apply (decompositionBasis m p).ext
  rintro ⟨t, q⟩
  rw [Module.Basis.rationalDiagonal_basis]
  have hm := decompositionBasis_mem N m p hN t q
  change decompositionBasis m p ⟨t, q⟩ ∈
    Auxiliary.chainPiece (N * (m + p) - m) (m + p)
      (decompositionDegree N m p ⟨t, q⟩).1 (decompositionDegree N m p ⟨t, q⟩).2 at hm
  split_ifs with he
  · simp only [he] at hm
    simpa only [one_smul] using Auxiliary.homogeneousProjection_eq_self hm
  · simpa only [zero_smul] using Auxiliary.homogeneousProjection_eq_zero_of_mem hm he

@[simp] theorem decompositionBasis_repr (m p : ℕ) (x : A (m + p))
    (t : ChainIndex p) (q : ChainIndex m) :
    (decompositionBasis m p).repr x ⟨t, q⟩ =
      (rationalChainBasis m).repr (decomposeChains m p x t) q := by
  simp [decompositionBasis, Module.Basis.map_repr, Finsupp.basis_repr]

/-- A nonzero coefficient of a homogeneous auxiliary chain has the prescribed
combined passive/active weight and exterior degree. -/
theorem component_support_degree (N m p w h : ℕ) (hN : 0 < N) {x : A (m + p)}
    (hx : x ∈ Auxiliary.chainPiece (N * (m + p) - m) (m + p) w h)
    (t : ChainIndex p) (q : ChainIndex m)
    (hq : (rationalChainBasis m).repr (decomposeChains m p x t) q ≠ 0) :
    decompositionDegree N m p ⟨t, q⟩ = (w, h) := by
  classical
  have he := congrArg (fun y => (decompositionBasis m p).repr y ⟨t, q⟩)
    (Auxiliary.homogeneousProjection_eq_self hx)
  rw [auxiliaryProjection_eq_diagonal N m p w h hN,
    Module.Basis.repr_rationalDiagonal] at he
  by_contra hn
  rw [if_neg hn, zero_mul, decompositionBasis_repr] at he
  exact hq he.symm

/-- Only active tridegrees compatible with the passive monomial can contribute
to a homogeneous auxiliary chain. Addition-based constraints avoid truncation. -/
theorem component_projection_eq_zero (N m p w h a b k : ℕ) (hN : 0 < N)
    {x : A (m + p)}
    (hx : x ∈ Auxiliary.chainPiece (N * (m + p) - m) (m + p) w h)
    (t : ChainIndex p)
    (hne : ¬ (passiveWeight N m p t + (m + p) * a = w + b ∧ k + t.2.card = h)) :
    homogeneousProjection N m a b k (decomposeChains m p x t) = 0 := by
  classical
  apply (rationalChainBasis m).repr.injective
  ext q
  rw [repr_homogeneousProjection, map_zero, Finsupp.zero_apply]
  split_ifs with hq
  · by_contra hn
    have hd := component_support_degree N m p w h hN hx t q hn
    have hw := activeWeight_add_weight N m (m + p) hN (Nat.le_add_right m p) q
    have hq' : monomialDegree N q = (a, b, k) := hq
    have hk : q.2.card = k := congrArg (fun i => i.2.2) hq'
    have hdw := congrArg Prod.fst hd
    have hdh := congrArg Prod.snd hd
    simp only [decompositionDegree] at hdw hdh
    simp only [hq'] at hw
    apply hne
    constructor <;> omega
  · rfl

end TorusLinkHomology.HilbertSeries.GeneralReversal
