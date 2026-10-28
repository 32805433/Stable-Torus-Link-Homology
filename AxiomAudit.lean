import TorusLinkHomology

/-! Check the transitive axiom dependencies of the three public theorems and
the two stable-series corollaries. This audit does not compare statements or
certify their correspondence with informal mathematics. -/

open Lean

run_cmd do
  for name in [``TorusLinkHomology.homology_generated_by_mu,
      ``TorusLinkHomology.HilbertSeries.finite_hilbert_series,
      ``TorusLinkHomology.HilbertSeries.stable_homology_coefficient,
      ``TorusLinkHomology.HilbertSeries.stable_charge_series,
      ``TorusLinkHomology.HilbertSeries.fermionicCoefficient_coeff_nat] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"{name} depends on axioms: {axioms}"
