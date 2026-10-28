# Verification

The maintained proof consists of `Generation.lean`, `HilbertSeries.lean`,
`TorusLinkHomology.lean`, `TorusLinkHomology/`, `DGA.lean`, and `DGA/`.
The project pins Lean **4.33.1** and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`.

## Reproduce the checks

From the repository root:

```sh
lake exe cache get
lake --wfail build
lake env lean AxiomAudit.lean
lake build Challenge
```

The default build includes all maintained library modules, including helper
modules not imported by the public theorems. It excludes Challenge. The
`--wfail` option makes warnings in the library build fail the command.

Lake reuses current build artifacts. For a fresh local-source build, move
`.lake/build` aside before running the commands; the dependency cache under
`.lake/packages` can remain. The public build and audit require no files
from the local, unpublished `proof/` directory.

## Axiom audit

[AxiomAudit.lean](AxiomAudit.lean) uses `Lean.collectAxioms` to traverse the
proof dependencies of:

- `TorusLinkHomology.homology_generated_by_mu`;
- `TorusLinkHomology.HilbertSeries.finite_hilbert_series`;
- `TorusLinkHomology.HilbertSeries.stable_homology_coefficient`;
- `TorusLinkHomology.HilbertSeries.stable_charge_series`;
- `TorusLinkHomology.HilbertSeries.fermionicCoefficient_coeff_nat`.

The audit prints the dependencies and fails on any axiom other than
`propext`, `Classical.choice`, and `Quot.sound`. In particular, it rejects
`sorryAx` and any project-specific axiom in those dependency chains.

A supplementary source scan can check for admissions and axiom declarations:

```sh
rg -n '\bsorry\b|\badmit\b|sorryAx|^\s*axiom\b' \
  Generation.lean HilbertSeries.lean TorusLinkHomology.lean \
  TorusLinkHomology DGA.lean DGA AxiomAudit.lean -g '*.lean'
```

No matches are expected (ripgrep then exits with status 1). This textual
scan is supplementary to the transitive axiom check.

## Independent statements

`Challenge.lean` is preserved independently of the implementation and imports
only Mathlib and the shared DGA infrastructure. Its three intentional proof
placeholders produce three warnings when `lake build Challenge` runs.
Challenge is never imported by the proof library or axiom audit.

Compiling Challenge checks that its declarations elaborate. It does not
compare its definitions or statements with the implementation. This repository
does not run an external comparator or publish a structural statement audit.
Lean compilation establishes the encoded propositions; correspondence with
the intended mathematics requires reviewing their statements and referenced
definitions.

## Maintenance

After changing the library, run the commands above. Preserve public theorem
names, statements, and mathematical definitions during organizational edits.
`Challenge.lean` and the shared DGA files are protected reference files and
must not be edited without explicit permission.

Informal proof writeups, manuscript assets, and the historical statement
archive remain local and are excluded from publication. They are not required
for any command documented here.
