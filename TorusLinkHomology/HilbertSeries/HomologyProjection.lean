import TorusLinkHomology.HilbertSeries.GradedDifferential

/-! Rational homogeneous projections on the actual total homology quotient. -/

noncomputable section
open scoped BigOperators
namespace TorusLinkHomology.HilbertSeries
open CoordinateKoszul

def totalClassMap (N n : ℕ) : (torusLinkDGA N n).cycles →ₗ[ℚ] Homology N n :=
  (torusLinkDGA N n).homologyClass.toLinearMap.restrictScalars ℚ

theorem totalClassMap_surjective (N n : ℕ) : Function.Surjective (totalClassMap N n) :=
  (torusLinkDGA N n).homologyClass_surjective

private theorem projection_cycle (N n a b h : ℕ) (x : (torusLinkDGA N n).cycles) :
    d N n (homogeneousProjection N n a b h x.val) = 0 := by
  cases h with
  | zero => exact d_eq_zero_of_mem_chainPiece_zero (homogeneousProjection_mem _ _ _ _ _ _)
  | succ h =>
    rw [← homogeneousProjection_d]
    have hx : d N n x.val = 0 := x.property
    rw [hx, map_zero]

def cycleProjection (N n a b h : ℕ) :
    (torusLinkDGA N n).cycles →ₗ[ℚ] (torusLinkDGA N n).cycles where
  toFun x := ⟨homogeneousProjection N n a b h x.val, projection_cycle N n a b h x⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' q x := by apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem coe_cycleProjection (N n a b h : ℕ) (x : (torusLinkDGA N n).cycles) :
    (cycleProjection N n a b h x : A n) = homogeneousProjection N n a b h x := rfl

private theorem projection_class_kernel (N n a b h : ℕ) :
    LinearMap.ker (totalClassMap N n) ≤
      LinearMap.ker ((totalClassMap N n).comp (cycleProjection N n a b h)) := by
  intro x hx
  change (torusLinkDGA N n).homologyClass x = 0 at hx
  change (torusLinkDGA N n).homologyClass (cycleProjection N n a b h x) = 0
  rw [(torusLinkDGA N n).homologyClass_eq_zero_iff] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  refine ⟨homogeneousProjection N n a b (h + 1) y, ?_⟩
  change d N n _ = homogeneousProjection N n a b h x.val
  rw [← homogeneousProjection_d]
  exact congrArg (homogeneousProjection N n a b h) hy

/-- Homogeneous projection descends through the actual cycle/boundary quotient. -/
def homologyProjection (N n a b h : ℕ) : Homology N n →ₗ[ℚ] Homology N n :=
  ((LinearMap.ker (totalClassMap N n)).liftQ
    ((totalClassMap N n).comp (cycleProjection N n a b h))
    (projection_class_kernel N n a b h)).comp
      ((totalClassMap N n).quotKerEquivOfSurjective (totalClassMap_surjective N n)).symm.toLinearMap

@[simp] theorem homologyProjection_class (N n a b h : ℕ) (x : (torusLinkDGA N n).cycles) :
    homologyProjection N n a b h ((torusLinkDGA N n).homologyClass x) =
      (torusLinkDGA N n).homologyClass (cycleProjection N n a b h x) := by
  change homologyProjection N n a b h (totalClassMap N n x) = _
  simp only [homologyProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  rfl

theorem homologyProjection_mem (N n a b h : ℕ) (x : Homology N n) :
    homologyProjection N n a b h x ∈ homologyPiece N n a b h := by
  obtain ⟨z, rfl⟩ := (torusLinkDGA N n).homologyClass_surjective x
  rw [homologyProjection_class]
  exact Submodule.mem_map.mpr ⟨cycleProjection N n a b h z,
    homogeneousProjection_mem _ _ _ _ _ _, rfl⟩

theorem homologyProjection_eq_self {N n a b h : ℕ} {x : Homology N n}
    (hx : x ∈ homologyPiece N n a b h) : homologyProjection N n a b h x = x := by
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
  change homologyProjection N n a b h ((torusLinkDGA N n).homologyClass z) = _
  rw [homologyProjection_class]
  change (torusLinkDGA N n).homologyClass (cycleProjection N n a b h z) =
    (torusLinkDGA N n).homologyClass z
  apply congrArg (torusLinkDGA N n).homologyClass
  apply Subtype.ext
  exact homogeneousProjection_eq_self hz

theorem homologyProjection_eq_zero_of_mem {N n a b h a' b' h' : ℕ} {x : Homology N n}
    (hx : x ∈ homologyPiece N n a b h) (hne : (a, b, h) ≠ (a', b', h')) :
    homologyProjection N n a' b' h' x = 0 := by
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
  change homologyProjection N n a' b' h' ((torusLinkDGA N n).homologyClass z) = _
  rw [homologyProjection_class]
  have he : cycleProjection N n a' b' h' z = 0 := by
    apply Subtype.ext
    exact homogeneousProjection_eq_zero_of_mem hz hne
  rw [he, map_zero]

theorem range_homologyProjection (N n a b h : ℕ) :
    LinearMap.range (homologyProjection N n a b h) = homologyPiece N n a b h := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact homologyProjection_mem _ _ _ _ _ _
  · intro x hx
    exact ⟨x, homologyProjection_eq_self hx⟩

/-- The finite set of degrees in any representative suffices to recover its class. -/
theorem sum_homologyProjection_class (N n : ℕ) (z : (torusLinkDGA N n).cycles) :
    ∑ d ∈ ((rationalChainBasis n).repr z.val).support.image (monomialDegree N),
      homologyProjection N n d.1 d.2.1 d.2.2 ((torusLinkDGA N n).homologyClass z) =
        (torusLinkDGA N n).homologyClass z := by
  simp only [homologyProjection_class, ← map_sum]
  congr 1
  apply Subtype.ext
  change (torusLinkDGA N n).cycles.val (∑ d ∈
    ((rationalChainBasis n).repr z.val).support.image (monomialDegree N),
      cycleProjection N n d.1 d.2.1 d.2.2 z) = z.val
  rw [map_sum]
  exact sum_homogeneousProjection N n z.val

/-- Every total homology class has a finite homogeneous decomposition. -/
theorem exists_sum_homologyProjection (N n : ℕ) (x : Homology N n) :
    ∃ s : Finset (ℕ × ℕ × ℕ), ∑ d ∈ s, homologyProjection N n d.1 d.2.1 d.2.2 x = x := by
  obtain ⟨z, rfl⟩ := (torusLinkDGA N n).homologyClass_surjective x
  exact ⟨_, sum_homologyProjection_class N n z⟩

theorem homologyProjection_comp (N n a b h a' b' h' : ℕ) :
    (homologyProjection N n a' b' h').comp (homologyProjection N n a b h) =
      if (a, b, h) = (a', b', h') then homologyProjection N n a b h else 0 := by
  classical
  ext x
  simp only [LinearMap.comp_apply]
  split_ifs with he
  · have ha := congrArg Prod.fst he
    have hb := congrArg (fun d => d.2.1) he
    have hh := congrArg (fun d => d.2.2) he
    dsimp only at ha hb hh
    subst a'
    subst b'
    subst h'
    exact homologyProjection_eq_self (homologyProjection_mem _ _ _ _ _ _)
  · exact homologyProjection_eq_zero_of_mem (homologyProjection_mem _ _ _ _ _ _) he

/-- Any finite set containing all nonzero homogeneous components recovers the class. -/
theorem sum_homologyProjection_of_support (N n : ℕ) (x : Homology N n)
    (s : Finset (ℕ × ℕ × ℕ))
    (hs : ∀ d ∉ s, homologyProjection N n d.1 d.2.1 d.2.2 x = 0) :
    ∑ d ∈ s, homologyProjection N n d.1 d.2.1 d.2.2 x = x := by
  classical
  obtain ⟨t, ht⟩ := exists_sum_homologyProjection N n x
  have hout (d : ℕ × ℕ × ℕ) (hd : d ∉ t) :
      homologyProjection N n d.1 d.2.1 d.2.2 x = 0 := by
    calc
      _ = homologyProjection N n d.1 d.2.1 d.2.2
          (∑ e ∈ t, homologyProjection N n e.1 e.2.1 e.2.2 x) := by rw [ht]
      _ = ∑ e ∈ t, homologyProjection N n d.1 d.2.1 d.2.2
          (homologyProjection N n e.1 e.2.1 e.2.2 x) := map_sum _ _ _
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        apply homologyProjection_eq_zero_of_mem (homologyProjection_mem _ _ _ _ _ _)
        simpa only [Prod.eta] using (show e ≠ d from fun h => hd (h ▸ he))
  calc
    (∑ d ∈ s, homologyProjection N n d.1 d.2.1 d.2.2 x) =
        ∑ d ∈ s ∪ t, homologyProjection N n d.1 d.2.1 d.2.2 x := by
      apply Finset.sum_subset Finset.subset_union_left
      intro d hd hds
      exact hs d hds
    _ = ∑ d ∈ t, homologyProjection N n d.1 d.2.1 d.2.2 x := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro d hd hdt
      exact hout d hdt
    _ = x := ht

end TorusLinkHomology.HilbertSeries
