import TorusLinkHomology.HilbertSeries.GradedDifferential
import TorusLinkHomology.HilbertSeries.FiniteRecurrence
import TorusLinkHomology.HilbertSeries.ShortRange
import TorusLinkHomology.HilbertSeries.FiniteCoordinateCase
import TorusLinkHomology.HilbertSeries.AuxiliaryDimensions
import TorusLinkHomology.HilbertSeries.Reversal
import TorusLinkHomology.HilbertSeries.QSeries.Specialization
import TorusLinkHomology.HilbertSeries.AuxiliaryRecurrence

noncomputable section

open scoped BigOperators

namespace TorusLinkHomology.HilbertSeries

private theorem d_empty (N : ℕ) (x : A 0) : d N 0 x = 0 := by
  induction x using CoordinateKoszul.induction_on_generators 0 with
  | hone => simp [d]
  | hadd x y hx hy => simp [hx, hy]
  | hsmul r x hx => simp [hx]
  | hxi i x hx => exact Fin.elim0 i

/-- Empty complexes have exactly the scalar homology class. -/
theorem homologyDimension_empty (N a b h : ℕ) :
    homologyDimension N 0 a b h = if a = 0 ∧ b = 0 ∧ h = 0 then 1 else 0 := by
  classical
  by_cases habh : a = 0 ∧ b = 0 ∧ h = 0
  · obtain ⟨rfl, rfl, rfl⟩ := habh
    rw [if_pos ⟨rfl, rfl, rfl⟩]
    have hk : LinearMap.ker (cycleClassMap N 0 0 0 0) = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      change (torusLinkDGA N 0).homologyClass x.val = 0 at hx
      obtain ⟨y, hy⟩ := (torusLinkDGA N 0).homologyClass_eq_zero_iff x.val |>.mp hx
      have hx0 : x.val.val = 0 := (d_empty N y).symm.trans hy |>.symm
      exact Subtype.ext (Subtype.ext hx0)
    have he := finrank_cyclePiece N 0 0 0 0
    rw [hk, finrank_bot, add_zero] at he
    rw [← he, ← finrank_chainPiece_zero, finrank_chainPiece]
    have hs : Subsingleton {m : BoundedMonomial 0 0 // HasDegree N 0 0 0 0 m} :=
      inferInstance
    have hn : Nonempty {m : BoundedMonomial 0 0 // HasDegree N 0 0 0 0 m} :=
      ⟨⟨(fun i => Fin.elim0 i, ∅), by simp [HasDegree]⟩⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨hs, hn⟩
  · rw [if_neg habh]
    apply homologyDimension_eq_zero_of_chainPiece_eq_bot
    apply chainPiece_eq_bot_of_no_degree
    intro m hm
    have hm0 : m.2 = ∅ := Subsingleton.elim _ _
    have ha := hm.1
    have hb := hm.2.1
    have hh := hm.2.2
    simp only [hm0, Finset.card_empty, mul_zero, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero] at ha hb hh
    exact habh ⟨ha.symm, hb.symm, hh.symm⟩

@[simp] theorem hilbertSeries_empty (N : ℕ) : hilbertSeries N 0 = 1 := by
  classical
  ext e
  have he : e = 0 ↔ e 0 = 0 ∧ e 1 = 0 ∧ e 2 = 0 := by
    constructor
    · rintro rfl; simp
    · rintro ⟨h0, h1, h2⟩
      ext i
      fin_cases i <;> assumption
  rw [MvPowerSeries.coeff_one]
  change (homologyDimension N 0 (e 0) (e 1) (e 2) : ℚ) = _
  simp [homologyDimension_empty, he]

@[simp] theorem finiteNumerator_empty (N : ℕ) : finiteNumerator N 0 = 1 := by
  classical
  simp only [finiteNumerator, Finset.range_one, Finset.sum_singleton, mul_zero, zero_add]
  rw [Finset.sum_eq_single 0]
  · simp [quadraticExponent, numeratorCorrection]
  · intro j hj hj0
    simp [hj0]
  · simp

/-- The empty-length case of the finite formula needs no positivity hypothesis. -/
theorem finite_hilbert_series_empty (N : ℕ) :
    qPochhammer (MvPowerSeries.X 0 : Series) (MvPowerSeries.X 1) 0 *
      hilbertSeries N 0 = finiteNumerator N 0 := by simp

end TorusLinkHomology.HilbertSeries
