# Reinhardt improved packing-density bound

**The requested lower-bound formalization is complete.** The final theorem is
`Certificate.Packing.reinhardt_density_lower_bound` in
`Certificate/ReinhardtDensityBound.lean`:

```lean
theorem reinhardt_density_lower_bound (K : Set E) (hK : IsSymmetricConvexDisc K) :
    (8950112 : ℝ) / 10000000 < packingDensity K
```

Here `E` is the Euclidean plane. The hypothesis says that K is compact, convex,
has nonempty interior, and is symmetric about the origin. `packingDensity` is
the original benchmark definition: the supremum of ball-limsup densities of
packings by congruent copies. The final theorem has no assumed minimizing body,
trajectory, boundary presentation, regularity, or published geometric lemma.
The corresponding universal `hexagonRatio` lower bound is also proved.

This verifies the improved universal lower bound 0.8950112. It is not the
Reinhardt conjecture identifying the optimal shape. The certificate is the
fixed supplied certificate; the optimization that discovered it is not rerun.

The combined audit covers **527 named targets**. Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted. The numerical checks use
kernel-checked exact arithmetic, with no `native_decide`, custom axioms, or
unfinished proofs in the production sources. See `logs/final/verification.json`
for the source/artifact manifest and exact axiom dependencies. Development
history and intermediate assumption boundaries remain in `WORK_LOG.md`.

## Proof chain

1. The supplied certificate is checked exactly: 248 Gram matrices, 248 Gram
   expansions, 75 multipliers, four polynomial reductions, and four assembled
   inequalities. The potential has 255 rational monomials and denominator 2^40;
   its cleared differential and boundary certificates have degree six.
2. Potential integration proves the trajectory cost bound. The published
   compact-domain confinement and the Hales–Vajjha area estimate are proved,
   including the geometric contact, area, and overlap arguments. Curvature and
   simplex controls are derived from convexity and the constructed frame.
3. Compactness and lower semicontinuity construct a global minimizer of the
   area/minimum-enclosing-hexagon-area ratio. Its hexagon infimum is attained
   and normalized to 2*sqrt(3). Irreducibility, full critical-midpoint boundary
   coverage, unique support lines, and the ordered sixfold successor are proved.
4. Exact support variation and compactness yield globally Lipschitz support
   gradients and tangents. The explicit radial angular curve and its five
   balanced companions have absolutely continuous actual velocities.
5. Integrating a positive periodic speed constructs a global C1 clock with a
   C1 inverse. After this time change, the adjacent velocity determinant is
   sqrt(3)/2. Absolute continuity is preserved by a proved disjoint-interval
   transport lemma.
6. The two neighboring curves determine a matrix state with AC coordinates,
   both determinant constraints, and the group ODE. The strict supporting
   inequalities prove all three star coordinates are positive.
7. The fundamental endpoint is the actual successor of the initial point;
   its angle is constructed in (0,pi), without assuming equal angular spacing.
   Positive tangent transport and fixed determinant force exact endpoint
   velocity matching. Constant left normalization gives initial identity and
   the rotated terminal state, constructing `minimizerFrameTrajectory`.
8. The initial arc parametrizes exactly its open sector, without repeats.
   Its six successor images cover all six sectors and their endpoints. Linear
   sign tests prove sector interiors disjoint, constructing `minimizerFrameTrace`.
9. The certificate bound transfers from this minimizer to every symmetric
   convex disc by global ratio minimality. The separately proved comparison
   with concrete hexagonal lattice packings gives the original packing-density
   bound. No optimality of lattice packings is assumed.

## Final construction files

| File | Verified role |
|---|---|
| `Certificate/ReinhardtDensityBound.lean` | Unconditional packing-density and hexagon-ratio bounds |
| `Certificate/MinimizerFrameTrace.lean` | Boundary coverage and disjoint, injective arc interiors |
| `Certificate/CriticalMidpointFundamentalPartition.lean` | Six sectors and their separating midpoints cover the boundary |
| `Certificate/CriticalMidpointSectorSeparation.lean` | Six explicit sign tests prove sector disjointness |
| `Certificate/MinimizerFundamentalArc.lean` | Exact sector range and injectivity of the initial arc |
| `Certificate/MinimizerFundamentalAngle.lean` | Actual successor endpoint and positive duration |
| `Certificate/MinimizerEndpointVelocities.lean` | Unique normalized tangent speed and endpoint velocity matching |
| `Certificate/InitialFrameNormalization.lean` | Area-preserving initial normalization and transformed convex body |
| `Certificate/MinimizerTerminalState.lean` | Rotated terminal state and complete `FrameTrajectory` |
| `Certificate/MinimizerStateStars.lean` | Strict star signs for the constructed state |
| `Certificate/MinimizerBalancedState.lean` | AC state coordinates, determinants, and group ODE |
| `Certificate/MinimizerClockInverse.lean` | Actual inverse-clock parametrization |
| `Certificate/MinimizerBalancedRegularity.lean` | Absolute continuity after reparametrization |
| `Certificate/PackingFromConstructedMinimizer.lean` | Previously conditional universal reduction, now instantiated |
| `Certificate/PackingDefinitions.lean` | Original benchmark definitions, without its placeholder conjecture |
| `Certificate.lean` | Root import of the completed result |

## Reproduce the build

Pinned versions: Lean `leanprover/lean4:v4.33.0`, mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.

The tested workflow reuses the existing read-only compiled mathlib cache. Set
`REINHARDT_CACHED_PROJECT` to another matching cache when moving the project.
No changes are made to that external cache. For already checked components:

```sh
python3 scripts/build_sos_assembly.py --identity H1_0 --resume
python3 scripts/build_sos_assembly.py --identity H1_1 --resume
python3 scripts/build_sos_assembly.py --identity H1_2 --resume
python3 scripts/build_sos_assembly.py --identity H2 --resume
python3 scripts/ensure_cached_module.py Mathlib.Analysis.Convex.Measure
python3 scripts/verify_certificate.py --audit-built
python3 scripts/status.py
```

`--audit-built` requires the local modules to have been compiled already. It
rebuilds the root and runs a fresh axiom audit of all 527 named targets, rejecting
stale local imports. It avoids rerunning expensive proof searches for unchanged
certificates. Without this option the verifier recompiles the final proof stages.

`python3 scripts/verify_certificate.py --rebuild-local` walks the complete local
import graph in dependency order and verifies every local module, reusing only
eligible content-cache hits. This is the longer replay option. A separate clean
standalone `lake build` has not been validated; `lakefile.toml` pins its dependency.

The final verifier checks the original-input and exact-certificate hashes, audits
527 named targets, and writes `logs/final/verification.json` only after every
stage passes. That report records the verified unconditional theorem alongside the earlier
conditional interfaces. It also records all local Lean sources and compiled
artifacts used by the final theorem.


## Verification and provenance

The final continuation uses a checked incremental build: every new component
is compiled with the pinned Lean toolchain, followed by a fresh root build and
combined axiom audit. Prior non-root modules are preserved byte-for-byte in
the source/artifact/companion manifest. This is not a claim that every unchanged
certificate was recompiled from scratch during the continuation.

`data/source_manifest.json` hashes the ten original inputs.
`data/exact/manifest.json` hashes the four exact reconstructed certificates.
The packing-definition body is checked against its original source hash.
`data/published_geometry_provenance.json` records the completed geometric
components and has an empty remaining-input list.

Current completion evidence:

- `logs/final/verification.json`
- `logs/final_unconditional_audit.log`
- `logs/unconditional_new_targets.json`
- `logs/unconditional_source_scan.json`
- `logs/unconditional_status.json`
- `logs/unconditional_final_integrity.json`

The verification and status tools now set the constructed-frame and
unconditional-packing flags from the audited final declarations. Status checks
source, artifact, and provenance hashes before reporting those flags as true.

## Efficient checked builds

The exact certificate uses sparse polynomial merging, row witnesses, and
checked trees of additions for its largest Gram expansions. Component reuse
is bound to source content, compiler options, and dependency artifacts.
Queue time is recorded separately from compiler time. Build validation reads
one metadata snapshot per run instead of repeatedly decoding each cache file.
These optimizations preserve kernel verification and certificate coefficients.

For the geometric assembly, explicit determinant identities and linear
combinations replace broad nonlinear proof search. The final state algebra
checks in about ten seconds on the recorded local run; individual timings and
failed-attempt history are in `WORK_LOG.md` and the component build logs.

## Independent proof verification

On 2026-10-30, the theorem `Certificate.Packing.reinhardt_density_lower_bound`
passed standard upstream Comparator, including Lean kernel replay, and Nanoda.
Nanoda checked 137,417 declarations, including dependencies. The successful run
took 3 hours, 3 minutes, 49 seconds. Both checkers used identical exported proof
bytes; the source/artifact, harness, and executable integrity checks passed.

See [the verification report](verification/report.txt),
[structured results](verification/report.json), and
[full checker log](verification/comparator/recorded/20261030T092754Z/reinhardt/check.log).
The check ran on macOS using the upstream development launcher, without Linux
sandbox isolation; proof-checking rules and the strict axiom policy were unchanged.
Nanoda used two workers and the documented worker-stack resource adjustment.

## Repository contents and reproduction requirements

This repository contains the Lean sources, fixed certificate inputs, exact data,
generation/build scripts, vendored Mathlib source modules, and recorded verification
evidence. `publication-manifest.json` records the hashes of the files copied from
the verified working directory. All audited proof sources were copied unchanged.
The original benchmark is preserved in `reference/028_reinhardt.lean`; its `sorry`
is the original open-problem placeholder, outside the production library.

Compiled `.olean` files, local caches, and exported proof streams are omitted from
Git. Their recorded hashes remain in the audit manifests and checker receipts.
The source snapshot also retains earlier generated Lean variants for development
history; the exact audited dependency graph is listed in
`logs/final/verification.json`.

A fresh clone therefore needs compilation before `--audit-built` can be used.
The tested scripts require a matching compiled Lean 4.33.0 / pinned Mathlib project;
set `REINHARDT_CACHED_PROJECT` to its absolute directory. See the build instructions
above for `--rebuild-local`. A clean standalone `lake build` has not been validated.
The independent-checker harness in `verification/comparator/` preserves the exact
configuration used for the recorded run. Its `paths.json` and historical provenance
contain workstation-specific paths; configure those paths for a new workstation.
The historical integrity receipts refer to the original compiled objects, which
are not distributed in this Git repository. New compilation/checks should produce
new receipts rather than overwrite the historical evidence.
