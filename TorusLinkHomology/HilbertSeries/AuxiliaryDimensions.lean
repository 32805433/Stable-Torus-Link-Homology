import TorusLinkHomology.HilbertSeries.AuxiliaryProjectionGrading
import TorusLinkHomology.HilbertSeries.AuxiliaryConnecting

/-! Rational linear maps between the finite auxiliary homogeneous homology spaces. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
namespace TorusLinkHomology.HilbertSeries.Auxiliary

/-- Injectivity and grading preservation let us recover homogeneity before J. -/
theorem J_reflects_chainPiece {N ell r w h : ℕ}
    (hi : Function.Injective (CoefficientComplex.J N r ell)) {x : A r}
    (hx : CoefficientComplex.J N r ell x ∈ chainPiece (ell - 1) r w h) :
    x ∈ chainPiece ell r w h := by
  have he : homogeneousProjection ell r w h x = x := by
    apply hi
    rw [← homogeneousProjection_J, homogeneousProjection_eq_self hx]
  rw [← he]
  exact homogeneousProjection_mem _ _ _ _ _

/-- A homogeneous middle lift gives a homogeneous connecting representative.
The middle lift has one more exterior factor than the connecting cycle. -/
theorem connectingRepresentative_mem_of_lift {N ell r w h : ℕ}
    (hm : ell + 1 < N * (r + 1)) {z u : A (r + 1)}
    (hu : u ∈ chainPiece ell (r + 1) w (h + 1))
    (he : CoefficientComplex.J N (r + 1) (ell + 1) z =
      CoefficientComplex.d N (r + 1) ell u) :
    z ∈ chainPiece (ell + 1) (r + 1) w h := by
  apply J_reflects_chainPiece (CoefficientComplex.J_injective N r ell hm)
  rw [he]
  simpa only [Nat.add_sub_cancel] using d_mem_chainPiece (N := N) hu

theorem comparisonHomology_mem {N ell r w h : ℕ}
    {x : (CoefficientComplex.dga N r ell).Homology}
    (hx : x ∈ homologyPiece N ell r w h) :
    CoefficientComplex.comparisonHomology N r ell x ∈ homologyPiece N (ell - 1) r w h := by
  obtain ⟨z, hz, rfl⟩ := hx
  change CoefficientComplex.comparisonHomology N r ell
    ((CoefficientComplex.dga N r ell).homologyClass z) ∈ _
  rw [CoefficientComplex.comparisonHomology_class]
  exact ⟨CoefficientComplex.comparisonCycles N r ell z, J_mem_chainPiece hz, rfl⟩

/-- The comparison map restricted to actual weight and exterior-degree homology. -/
def comparisonHomologyPiece (N ell r w h : ℕ) :
    homologyPiece N ell r w h →ₗ[ℚ] homologyPiece N (ell - 1) r w h where
  toFun x := ⟨CoefficientComplex.comparisonHomology N r ell x.val, comparisonHomology_mem x.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_rat_smul _ _ _)

/-- Tail generation and homogeneous projection prove surjectivity degree by degree. -/
theorem comparisonHomologyPiece_surjective (N ell r w h : ℕ) (hN : 0 < N)
    (hell : ell ≤ N * r) : Function.Surjective (comparisonHomologyPiece N ell r w h) := by
  intro x
  obtain ⟨z, hz, he⟩ := x.property
  have hzcycle : CoefficientComplex.d N r (ell - 1) z.val = 0 := z.property
  obtain ⟨v, hv, hc, u, hu, huv⟩ := comparison_homogeneous_cycle_lift N ell r w h hN hell hzcycle hz
  let vcycle : (CoefficientComplex.dga N r ell).cycles := ⟨v, hc⟩
  let vclass : homologyPiece N ell r w h :=
    ⟨(CoefficientComplex.dga N r ell).homologyClass vcycle, ⟨vcycle, hv, rfl⟩⟩
  refine ⟨vclass, Subtype.ext ?_⟩
  change CoefficientComplex.comparisonHomology N r ell
    ((CoefficientComplex.dga N r ell).homologyClass vcycle) = x.val
  rw [CoefficientComplex.comparisonHomology_class, ← he]
  apply (CoefficientComplex.dga N r (ell - 1)).homologyClass_eq_iff _ _ |>.mpr
  refine ⟨-u, ?_⟩
  change CoefficientComplex.d N r (ell - 1) (-u) = CoefficientComplex.J N r ell v - z.val
  rw [map_neg, huv]
  abel

/-- A homogeneous class in the kernel has a lift diagram with a homogeneous
middle primitive. This is the graded exactness input for the connecting image. -/
theorem comparisonHomologyPiece_kernel_lift (N ell r w h : ℕ)
    (x : homologyPiece N (ell + 1) (r + 1) w h)
    (hx : comparisonHomologyPiece N (ell + 1) (r + 1) w h x = 0) :
    ∃ z : (CoefficientComplex.dga N (r + 1) (ell + 1)).cycles,
      z ∈ cyclePiece N (ell + 1) (r + 1) w h ∧
      (CoefficientComplex.dga N (r + 1) (ell + 1)).homologyClass z = x.val ∧
      ∃ u ∈ chainPiece ell (r + 1) w (h + 1),
        CoefficientComplex.J N (r + 1) (ell + 1) z.val =
          CoefficientComplex.d N (r + 1) ell u := by
  obtain ⟨z, hz, he⟩ := x.property
  refine ⟨z, hz, he, ?_⟩
  have hx' := congrArg (fun y : homologyPiece N ((ell + 1) - 1) (r + 1) w h => y.val) hx
  change CoefficientComplex.comparisonHomology N (r + 1) (ell + 1) x.val = 0 at hx'
  rw [← he] at hx'
  change CoefficientComplex.comparisonHomology N (r + 1) (ell + 1)
    ((CoefficientComplex.dga N (r + 1) (ell + 1)).homologyClass z) = 0 at hx'
  rw [CoefficientComplex.comparisonHomology_class] at hx'
  obtain ⟨u, hu⟩ := (CoefficientComplex.dga N (r + 1) ell).homologyClass_eq_zero_iff
    (CoefficientComplex.comparisonCycles N (r + 1) (ell + 1) z) |>.mp hx'
  have hJ : CoefficientComplex.J N (r + 1) (ell + 1) z.val ∈ chainPiece ell (r + 1) w h :=
    J_mem_chainPiece (N := N) (ell := ell + 1) (r := r + 1) (w := w) (h := h) (x := z.val) hz
  change CoefficientComplex.d N (r + 1) ell u = CoefficientComplex.J N (r + 1) (ell + 1) z.val at hu
  refine ⟨homogeneousProjection ell (r + 1) w (h + 1) u,
    homogeneousProjection_mem _ _ _ _ _, ?_⟩
  rw [← homogeneousProjection_d, hu, homogeneousProjection_eq_self hJ]

/-- The connecting cycle has the weight of the source plus the removed generator. -/
theorem connectingCycle_mem {N ell r w h : ℕ} (hm : ell + 1 < N * (r + 1))
    (a : (CoefficientComplex.dga N r (ell + 1)).cycles)
    (ha : a ∈ cyclePiece N (ell + 1) r w h) :
    CoefficientComplex.connectingCycle N r ell hm a ∈ cyclePiece N (ell + 1) (r + 1) (w + (ell + 1)) h := by
  apply connectingRepresentative_mem_of_lift hm _ (CoefficientComplex.J_connectingCycle N r ell hm a)
  have hl := mul_mem_chainPiece (xi_mem_chainPiece ell (r + 1) 0)
    (includeCommon_mem_chainPiece (show a.val ∈ chainPiece (ell + 1) r w h from ha))
  simpa only [Fin.val_zero, Nat.add_zero, Nat.add_comm] using hl

/-- The connecting map respects homogeneous homology, with its positive weight shift. -/
theorem connectingHomology_mem {N ell r w h : ℕ} (hm : ell + 1 < N * (r + 1))
    {x : (CoefficientComplex.dga N r (ell + 1)).Homology}
    (hx : x ∈ homologyPiece N (ell + 1) r w h) :
    CoefficientComplex.connectingHomology N r ell hm x ∈
      homologyPiece N (ell + 1) (r + 1) (w + (ell + 1)) h := by
  obtain ⟨a, ha, rfl⟩ := hx
  change CoefficientComplex.connectingHomology N r ell hm
    ((CoefficientComplex.dga N r (ell + 1)).homologyClass a) ∈ _
  rw [CoefficientComplex.connectingHomology_class]
  exact ⟨CoefficientComplex.connectingCycle N r ell hm a, connectingCycle_mem hm a ha, rfl⟩

/-- The connecting map restricted to finite homogeneous homology spaces. -/
def connectingHomologyPiece (N ell r w h : ℕ) (hm : ell + 1 < N * (r + 1)) :
    homologyPiece N (ell + 1) r w h →ₗ[ℚ]
      homologyPiece N (ell + 1) (r + 1) (w + (ell + 1)) h where
  toFun x := ⟨CoefficientComplex.connectingHomology N r ell hm x.val, connectingHomology_mem hm x.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem connectingHomologyPiece_injective (N ell r w h : ℕ) (hN : 0 < N)
    (hm : ell + 1 < N * (r + 1)) : Function.Injective (connectingHomologyPiece N ell r w h hm) := by
  intro x y hxy
  apply Subtype.ext
  apply CoefficientComplex.connectingHomology_injective N r ell hN hm
  exact congrArg (fun z : homologyPiece N (ell + 1) (r + 1) (w + (ell + 1)) h => z.val) hxy

/-- Exactness of the connecting map in each shifted homogeneous piece. -/
theorem range_connectingHomologyPiece (N ell r w h : ℕ) (hm : ell + 1 < N * (r + 1)) :
    LinearMap.range (connectingHomologyPiece N ell r w h hm) =
      LinearMap.ker (comparisonHomologyPiece N (ell + 1) (r + 1) (w + (ell + 1)) h) := by
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    apply Subtype.ext
    have he : CoefficientComplex.connectingHomology N r ell hm a.val ∈
        LinearMap.ker ((CoefficientComplex.comparisonHomology N (r + 1) (ell + 1)).restrictScalars ℚ) := by
      rw [← CoefficientComplex.range_connectingHomology N r ell hm]
      exact ⟨a.val, rfl⟩
    exact he
  · intro x hx
    obtain ⟨z, hz, he, u, hu, hJu⟩ :=
      comparisonHomologyPiece_kernel_lift N ell r (w + (ell + 1)) h x hx
    have ha : CoefficientComplex.d N r (ell + 1) (CoefficientComplex.p r u) = 0 := by
      have hp := congrArg (CoefficientComplex.p r) hJu
      rw [CoefficientComplex.p_J, CoefficientComplex.p_d] at hp
      exact neg_eq_zero.mp hp.symm
    let acycle : (CoefficientComplex.dga N r (ell + 1)).cycles := ⟨CoefficientComplex.p r u, ha⟩
    have haw : acycle ∈ cyclePiece N (ell + 1) r w h := p_mem_chainPiece hu
    let aclass : homologyPiece N (ell + 1) r w h :=
      ⟨(CoefficientComplex.dga N r (ell + 1)).homologyClass acycle, ⟨acycle, haw, rfl⟩⟩
    refine ⟨aclass, Subtype.ext ?_⟩
    change CoefficientComplex.connectingHomology N r ell hm
      ((CoefficientComplex.dga N r (ell + 1)).homologyClass acycle) = x.val
    rw [CoefficientComplex.connectingHomology_eq_class N r ell hm acycle z ⟨u, rfl, hJu⟩]
    exact he

/-- Dimension additivity for the auxiliary short exact sequence, using
addition-based indexing for the weight shift. -/
theorem homologyDimension_recurrence_shifted (N ell r w h : ℕ) (hN : 0 < N)
    (hm : ell + 1 < N * (r + 1)) :
    homologyDimension N (ell + 1) (r + 1) (w + (ell + 1)) h =
      homologyDimension N ell (r + 1) (w + (ell + 1)) h +
      homologyDimension N (ell + 1) r w h := by
  have hr := (comparisonHomologyPiece N (ell + 1) (r + 1) (w + (ell + 1)) h).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (comparisonHomologyPiece_surjective N (ell + 1) (r + 1)
    (w + (ell + 1)) h hN (Nat.le_of_lt hm)), finrank_top,
    ← range_connectingHomologyPiece N ell r w h hm,
    LinearMap.finrank_range_of_inj (connectingHomologyPiece_injective N ell r w h hN hm)] at hr
  exact hr.symm

/-- Below the connecting weight shift the comparison kernel is zero. -/
theorem ker_comparisonHomologyPiece_below_shift (N ell r w h : ℕ)
    (hm : ell + 1 < N * (r + 1)) (hw : w < ell + 1) :
    LinearMap.ker (comparisonHomologyPiece N (ell + 1) (r + 1) w h) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨z, hz, he, u, hu, hJu⟩ := comparisonHomologyPiece_kernel_lift N ell r w h x hx
  have hp : CoefficientComplex.p r u = 0 := p_eq_zero_of_low_degree hu (Or.inl hw)
  have hr : CoefficientComplex.ConnectingRepresentative N r ell 0 z.val := ⟨u, hp, hJu⟩
  obtain ⟨c, hc⟩ := hr.boundary_of_source_zero hm
  have hz0 : (CoefficientComplex.dga N (r + 1) (ell + 1)).homologyClass z = 0 :=
    (CoefficientComplex.dga N (r + 1) (ell + 1)).homologyClass_eq_zero_iff z |>.mpr ⟨c, hc.symm⟩
  exact Subtype.ext (he.symm.trans hz0)

theorem homologyDimension_recurrence_below_shift (N ell r w h : ℕ) (hN : 0 < N)
    (hm : ell + 1 < N * (r + 1)) (hw : w < ell + 1) :
    homologyDimension N (ell + 1) (r + 1) w h = homologyDimension N ell (r + 1) w h := by
  exact (LinearEquiv.ofBijective (comparisonHomologyPiece N (ell + 1) (r + 1) w h)
    ⟨LinearMap.ker_eq_bot.mp (ker_comparisonHomologyPiece_below_shift N ell r w h hm hw),
      comparisonHomologyPiece_surjective N (ell + 1) (r + 1) w h hN (Nat.le_of_lt hm)⟩).finrank_eq

/-- Coefficientwise form of the auxiliary recurrence, including all weights
below the shift, where the extra term is zero. -/
theorem homologyDimension_recurrence (N ell r w h : ℕ) (hN : 0 < N)
    (hm : ell + 1 < N * (r + 1)) :
    homologyDimension N (ell + 1) (r + 1) w h =
      homologyDimension N ell (r + 1) w h +
      if ell + 1 ≤ w then homologyDimension N (ell + 1) r (w - (ell + 1)) h else 0 := by
  by_cases hw : ell + 1 ≤ w
  · rw [if_pos hw]
    simpa only [Nat.sub_add_cancel hw] using
      homologyDimension_recurrence_shifted N ell r (w - (ell + 1)) h hN hm
  · rw [if_neg hw, Nat.add_zero]
    exact homologyDimension_recurrence_below_shift N ell r w h hN hm (by omega)

/-- Auxiliary Hilbert series in variables 0 = weight and 1 = exterior degree. -/
def hilbertSeries (N r ell : ℕ) : ChargeSeries :=
  fun e => (homologyDimension N ell r (e 0) (e 1) : ℚ)

/-- The auxiliary Hilbert-series recurrence proved from graded comparison
exactness. Multiplication by X₀^(ell+1) handles weights below the shift. -/
theorem hilbertSeries_recurrence (N ell r : ℕ) (hN : 0 < N)
    (hm : ell + 1 < N * (r + 1)) :
    hilbertSeries N (r + 1) (ell + 1) = hilbertSeries N (r + 1) ell +
      (MvPowerSeries.X 0 : ChargeSeries) ^ (ell + 1) * hilbertSeries N r (ell + 1) := by
  classical
  ext e
  rw [map_add, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul]
  have hle : Finsupp.single (0 : Fin 2) (ell + 1) ≤ e ↔ ell + 1 ≤ e 0 := by
    constructor
    · intro he; simpa using he 0
    · intro he i
      fin_cases i <;> simp [he]
  simp only [hle, MvPowerSeries.coeff_apply, hilbertSeries]
  rw [homologyDimension_recurrence N ell r (e 0) (e 1) hN hm, Nat.cast_add]
  split_ifs <;> simp [Finsupp.tsub_apply]

end TorusLinkHomology.HilbertSeries.Auxiliary
