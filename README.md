# Stable torus-link homology

Lean proofs over $`\mathbb{Q}`$ of generation and Hilbert-series formulas for
the Koszul algebra underlying stable torus-link homology. The project uses
Lean and Mathlib **4.33.1**.

## The Koszul algebra and its gradings

For $`N\geq 1`$ and $`n\geq 0`$, let

```math
R_n=\mathbb{Q}[u_0,\ldots,u_{n-1}],\qquad
K_{n,N}=R_n\otimes_{\mathbb{Q}}
\Lambda_{\mathbb{Q}}(\xi_0,\ldots,\xi_{n-1}).
```

The $`u_i`$ are even polynomial generators and the $`\xi_i`$ are odd exterior
generators. Set $`u(x)=\sum_{i=0}^{n-1}u_i x^i`$ and define the differential by

```math
d_N(u_i)=0,\qquad
d_N(\xi_i)=[x^i]u(x)^N
=\sum_{\substack{0\leq i_1,\ldots,i_N\lt n\\i_1+\cdots+i_N=i}}
u_{i_1}\cdots u_{i_N},
```

extended by the graded Leibniz rule. This is the Koszul complex of the
coefficient polynomials $`[x^i]u(x)^N`$. The model was proposed for $`N=2`$ by
[Gorsky–Oblomkov–Rasmussen](https://arxiv.org/abs/1206.2226), with its general
$`N`$ version described by [Gorsky–Lewark](https://arxiv.org/abs/1404.0623).
[Ballinger–Gorsky–Hogancamp–Wang](https://arxiv.org/html/2507.00175v1#S1)
identify its homology as the $`E_2`$ page of the stable Rasmussen spectral
sequence over $`\mathbb{Q}`$.

We use the trigrading $`(a,b,h)`$ given by

```math
\deg(u_i)=(1,i,0),\qquad \deg(\xi_i)=(N,i,1).
```

Here $`a`$ is the internal degree extending ordinary polynomial degree on
$`R_n`$, $`b`$ is the index weight, and $`h`$ is the exterior (Koszul) degree.
The differential has degree $`(0,0,-1)`$. In the quantum and cohomological
conventions of Ballinger–Gorsky–Hogancamp–Wang, the corresponding degrees are

```math
(Q,T)=(2(a+b),-2b-h).
```

Thus $`d_N`$ preserves $`Q`$ and raises $`T`$ by one. This cohomological degree
has the opposite sign to the positive homological grading used by
Gorsky–Oblomkov–Rasmussen.

For $`1\leq k\lt n`$, define

```math
\mu_k=\sum_{\substack{0\leq i,j\lt n\\i+j=k}}(Ni-j)u_i\xi_j.
```

These are cocycles: $`d_N(\mu_k)=0`$. Their tridegrees are $`(N+1,k,1)`$.

## Generation

For every $`N\geq 1`$ and $`n\geq 0`$, **the classes
$`[\mu_1],\ldots,[\mu_{n-1}]`$ generate $`H_*(K_{n,N},d_N)`$ as an
$`R_n`$-algebra**.

The public Lean theorem is
`TorusLinkHomology.homology_generated_by_mu` in
[Generation.lean](Generation.lean).

## Hilbert series and the infinite limit

For each finite $`n`$, the explicit trigrading above defines the Hilbert series

```math
f_{n,N}(s,v,z)=\sum_{a,b,h\geq 0}
\dim_{\mathbb{Q}}H_h(K_{n,N},d_N)_{a,b}\;s^a v^b z^h.
```

**Finite $`n`$.** For every $`n\geq 0`$ and $`N\geq 1`$, we prove
an explicit formula for $`f_{n,N}`$ in terms of finite products and Gaussian
binomial coefficients. It determines every trigraded homology dimension.
Through the stable torus-link identification discussed below, for $`n\geq 1`$
it gives the Poincaré series of the $`\mathfrak{gl}_N`$ homology of $`T(n,\infty)`$.
The public Lean theorem is
`TorusLinkHomology.HilbertSeries.finite_hilbert_series` in
[HilbertSeries.lean](HilbertSeries.lean).

**The limit $`n\to\infty`$.** For every $`N\geq 1`$, we prove that
$`f_{\infty,N}=\lim_{n\to\infty}f_{n,N}`$ exists coefficientwise, with every
coefficient of weight $`b`$ already stable for $`n\gt b`$. We give a fermionic
formula using Gordon multisums, whose nonnegative terms express the stable
dimensions without alternating cancellation. It describes the Poincaré series of the $`\mathfrak{gl}_N`$ homology of $`T(\infty,\infty)`$.
The public Lean theorem is
`TorusLinkHomology.HilbertSeries.stable_homology_coefficient` in
[HilbertSeries.lean](HilbertSeries.lean), which also contains the stable-series
equality and coefficient-integrality corollaries.

## Conjectures and the stable torus-link consequence

Over $`\mathbb{Q}`$, the generation theorem confirms
[Gorsky–Oblomkov–Rasmussen, Conjecture 3.12](https://arxiv.org/html/1206.2226v2#S3.SS3)
for $`N=2`$, [Gorsky–Lewark, Conjecture 4](https://arxiv.org/abs/1404.0623)
for general $`N`$, and its restatement as
[Ballinger–Gorsky–Hogancamp–Wang, Conjecture 7.4](https://arxiv.org/html/2507.00175v1#S7.SS1).

The $`N=2`$ Hilbert-series results confirm the finite-series prediction in
[Gorsky–Oblomkov–Rasmussen, Conjecture 1.7 (also 4.3)](https://arxiv.org/html/1206.2226v2#S1)
and the Khovanov–Rogers–Ramanujan identity of
[Conjecture 4.9](https://arxiv.org/html/1206.2226v2#S4), with the endpoint
correction that the middle summand in its displayed bosonic expression
$`B(a,q,t)`$ is omitted at $`p=0`$. The formulas here extend these results to
all $`N\geq 1`$.

Combining generation with
[Ballinger–Gorsky–Hogancamp–Wang, Theorems 1.1 and 7.5](https://arxiv.org/html/2507.00175v1#S7.SS1)
forces the stable Rasmussen spectral sequence to collapse at $`E_2`$.
Consequently, for $`n\geq 1`$, $`H_*(K_{n,N},d_N)`$ computes the rational stable
$`\mathfrak{gl}_N`$ Khovanov–Rozansky homology of $`T(n,\infty)`$ as a bigraded
vector space. This confirms the rational form of the stable torus-link
model conjecture of Gorsky–Oblomkov–Rasmussen (Conjecture 1.1) and its
general-$`N`$ version in Gorsky–Lewark (Conjecture 1). The Lean development
proves the algebraic results; the spectral-sequence and topological
identifications used for this consequence are results from the cited
literature, not formalized here.

[Challenge.lean](Challenge.lean) is a frozen independent statement file. It
imports Mathlib and the shared DGA infrastructure, without importing the
TorusLinkHomology implementation. Its three intentional `sorry` proofs are
problem placeholders, not dependencies of the proved library.

## Build and use

Install Lean through elan, then run:

```sh
lake exe cache get
lake --wfail build
lake env lean AxiomAudit.lean
```

The dependency versions are pinned by `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. To use the results:

```lean
import TorusLinkHomology  -- All three public results
```

Alternatively, import `Generation` or `HilbertSeries` separately. To check
that the frozen statements elaborate, run `lake build Challenge`; its three
intentional admission warnings are expected.

## Verification

The proof library contains no admissions or custom axioms.
[AxiomAudit.lean](AxiomAudit.lean) checks the transitive dependencies of all
three public theorems and both stable corollaries, rejecting every axiom
except `propext`, `Classical.choice`, and `Quot.sound`.

[VERIFICATION.md](VERIFICATION.md) documents how to run the checks locally
and explains their scope. There is no external comparator check.
Mathematical correspondence requires examining the theorem statements and
the definitions they reference.

## Layout

| Path | Role |
| --- | --- |
| `Generation.lean`, `HilbertSeries.lean` | Public theorem declarations |
| `TorusLinkHomology.lean` | Imports both public theorem modules |
| `TorusLinkHomology/Basic.lean`, `MuCycles.lean`, `Homology.lean` | Original complex, named cycles, and homology definitions |
| `TorusLinkHomology/Generation/` | Supporting generation proofs |
| `TorusLinkHomology/HilbertSeries/` | Supporting Hilbert-series definitions and proofs |
| `DGA.lean`, `DGA/` | Reusable differential graded algebra infrastructure |
| `Challenge.lean` | Frozen independent statements |
| `AxiomAudit.lean` | Executable axiom check |

## Authorship and license

The Lean formalization and documentation were developed with AI assistance
through Codex and Claude Code under human direction. Compilation and axiom checks do not
constitute independent human mathematical review.

The repository's own code and documentation are distributed under the
[MIT license](LICENSE). Lean, Mathlib, and their dependencies retain their
respective licenses.
