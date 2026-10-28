import TorusLinkHomology.Homology

open TorusLinkHomology

/-- The two formulations are equivalent independently of either generation theorem. -/
theorem equivalence (n N : ℕ) (hN : 0 < N) :
    ((∀ k : ℕ, 1 ≤ k → k < n → d N n (mu N n k) = 0) ∧
      (∀ a : A n, d N n a = 0 →
        ∃ p : A n, p ∈ muSubalgebra N n ∧ ∃ b : A n, a = p + d N n b)) ↔
    Algebra.adjoin (R n) (Set.range (muClass N n)) =
      (⊤ : Subalgebra (R n) (Homology N n)) := by
  have _positiveN : 0 < N := hN
  let D := torusLinkDGA N n
  let C : Subalgebra (R n) D.cycles :=
    Algebra.adjoin (R n) (Set.range (muCycle N n))
  -- The same generated algebra viewed inside A or inside homology.
  have hcycles : C.map D.cycles.val = muSubalgebra N n := by
    change (Algebra.adjoin (R n) (Set.range (muCycle N n))).map _ = _
    rw [AlgHom.map_adjoin]
    unfold muSubalgebra
    apply congrArg (Algebra.adjoin (R n))
    ext a
    constructor
    · rintro ⟨x, ⟨k, rfl⟩, ha⟩
      exact ⟨k.val, k.property.1, k.property.2, ha.symm⟩
    · rintro ⟨k, hk, hkn, rfl⟩
      exact ⟨muCycle N n ⟨k, hk, hkn⟩, ⟨⟨k, hk, hkn⟩, rfl⟩, rfl⟩
  have hhomology : C.map D.homologyClass =
      Algebra.adjoin (R n) (Set.range (muClass N n)) := by
    change (Algebra.adjoin (R n) (Set.range (muCycle N n))).map _ = _
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  constructor
  · rintro ⟨_, hgen⟩
    apply Algebra.eq_top_iff.mpr
    intro h
    obtain ⟨a, rfl⟩ := D.homologyClass_surjective h
    obtain ⟨p, hp, b, hab⟩ := hgen (a : A n) a.property
    have hp' : p ∈ C.map D.cycles.val := by rwa [hcycles]
    obtain ⟨c, hc, hcp⟩ := Subalgebra.mem_map.mp hp'
    have hac : D.homologyClass a = D.homologyClass c := by
      apply (D.homologyClass_eq_iff a c).mpr
      refine ⟨b, ?_⟩
      change d N n b = (a : A n) - (c : A n)
      change (c : A n) = p at hcp
      rw [hcp, hab, add_sub_cancel_left]
    rw [← hhomology, hac]
    exact Subalgebra.mem_map.mpr ⟨c, hc, rfl⟩
  · intro hgen
    refine ⟨fun k _ hk => mu_is_cycle N n k hk, ?_⟩
    intro a ha
    let aCycle : D.cycles := ⟨a, ha⟩
    have haClass : D.homologyClass aCycle ∈ C.map D.homologyClass := by
      rw [hhomology, hgen]
      trivial
    obtain ⟨c, hc, hca⟩ := Subalgebra.mem_map.mp haClass
    have hc' : (c : A n) ∈ muSubalgebra N n := by
      rw [← hcycles]
      exact Subalgebra.mem_map.mpr ⟨c, hc, rfl⟩
    obtain ⟨b, hb⟩ := (D.homologyClass_eq_iff aCycle c).mp hca.symm
    refine ⟨(c : A n), hc', b, ?_⟩
    change d N n b = a - (c : A n) at hb
    rw [hb, add_sub_cancel]
