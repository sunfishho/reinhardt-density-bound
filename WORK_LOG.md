# Verification work log and continuation notes

The current scope now includes continuing the published geometric inputs, as
requested after the fixed certificate and its new confinement proof were complete.
No `sorry`, additional axioms, or `native_decide` are allowed. Do not call the
unconditional convex-body packing theorem complete while the geometric inputs
listed in README remain unproved.

**Latest milestone (2026-10-27, geometric bridge):** nine new modules extend the
certificate to the original benchmark packing-density definition. They prove the
lattice-density comparison, hexagon packing construction, midpoint covolume
normalization, compact exclusion from the scalar area estimate, and reconstruction
of the controls from nonnegative curvature. The derivative of the determinant
constraint is derived a.e. from AC regularity. The highest-level result is
`Packing.packing_density_bound_of_curvature_data`; it remains conditional on the
balanced-disc construction, geometric area identity, and HV geometric area
estimate. The verifier now audits 32 named theorems. Check its current report
before treating the final assembly as freshly verified.

## Current authoritative project

This directory under `Downloads/Stanford/ai-for-math/convex-lean-eval/.../trajectories`
is the writable working project. The older visualization-directory copy is obsolete.
No applicable parent AGENTS.md was found. No subagents are authorized.

## Verified milestones

- The actual representative 104x104 block is PSD over the reals:
  `Certificate.BenchmarkLite.block0_posSemidef`, compiled in BenchmarkVerified.lean.
- The generalized pipeline independently checked H1_0 block 0 and is checking all 248.
  Run `python3 scripts/status.py` for current-source counts; do not count merely generated files.
- Matrix positivity soundness, correct denominator convex combination, absolutely
  continuous integration, exact decimal rounding, multiplier-product nonnegativity,
  and elementary determinant rewrites have passed. See README and logs/axiom_audit.log.
- Sparse polynomial arithmetic/evaluation soundness has passed. Its merge algorithm
  was changed from well-founded recursion to structurally recursive fuel to avoid
  repeated list-length computation in the kernel. The new proof passed (logs/sparse_polynomial.log).
- All four quotient/reduction checks passed with the old merge implementation. A fresh
  recheck with the new implementation is running. Count only its fresh reports under logs/ideals.
- SOSPolynomial.lean proves that the polynomial expansion of an actual Gram matrix
  is nonnegative from its PSD proof. H2 block 0 expansion/multiplication checks passed,
  with matrix PSD and multiplier nonnegativity as explicit inputs.

## Running work (revalidate handles; never restart just from an observation timeout)

At this checkpoint, unified exec sessions were:
- 67982: `python3 scripts/build_matrices.py --resume --skip H1_0:0`, logging logs/all_matrices.log.
- 33515: H1_2 matrix proofs, then H2, logging logs/matrices_H1_2.log and logs/matrices_H2.log.
  The main worker will reuse their reports when it reaches those identities.
- 51340: rebuild SOSPolynomial, then `scripts/build_ideal_checks.py`, logging
  logs/ideal_recheck.log and logs/ideals/*. This reruns all four reductions with the new checker.
- 6299: first H2 block SOS expansion prototype (likely completed; inspect its handle/log).

Compilation concurrency is now limited by OS locks in scripts/lean_cached.py; default
REINHARDT_LEAN_JOBS=1. This was necessary because simultaneous Lean jobs caused heavy
memory swapping. A waiting wrapper is not a dead build. The lock is released by the OS.

## Exact data and generators

- data/source contains the original scripts, targets, metadata and four .npz proposals.
  source_manifest.json hashes them; export_all.py uses the bundled copy by default.
- data/exact/H*.json: all 248 exact reconstructed matrices and approximate factor
  witnesses, verified by exact integer residual dominance in Python.
- scripts/emit_matrix_proofs.py -> Certificate/Generated, 248 matrix data/proof pairs.
- scripts/build_matrices.py records completed proof/audit/source hashes in logs/matrices.
  Use --resume, optional --identity/--block/--skip; stop at first compiler failure.
- data/polynomials/H*.json: raw target, recorded SOS polynomial, exact integer quotient
  witnesses for g11*g22-g12*g21-1, h^2-a^2-p^2-1, and t^2-3. Global denominator is 120 bits.
  All four ideal identities replay exactly in Python. This is witness generation, not optimization.
- Potential coefficients are in data/polynomials/potential.json, as an integer polynomial
  divided by one positive denominator. Source V has degree 4; certificate degree is 6.
- scripts/emit_ideal_checks.py -> Certificate/Identities. Their quotient_identity theorem
  compares raw target with recorded SOS plus the ideal multiples. It does NOT itself link
  recordedSOS to the Gram matrices or raw target to derivatives/boundary evaluation of V.
- scripts/emit_sos_checks.py -> Certificate/SOS, 248 data/proof pairs. gram_check links
  gramPolynomial of the actual GramData/basis to its recorded polynomial; weighted_check
  checks multiplication by the recorded multiplier. Only H2 block 0 has been run so far.

## Remaining proof chain (full scope)

1. Finish and audit all 248 matrix PSD proofs (already running).
2. Compile all Gram-polynomial expansion/multiplication checks. Begin with the 23 small
   H2 blocks. Then check each identity's recordedSOS is the sum of its scaled block
   polynomials. All data are already exported and the general soundness lemmas exist.
3. Connect recorded multiplier polynomials to the 19 primitive constraints. Names are
   single constraints or products of two. Primitive rational polynomials can be cleared
   by positive integer denominators. For products, the only reduction required is t^2=3;
   prove the small quotient identity with Sparse.checkEqual. The generic list-product
   nonnegativity theorem already exists in Multipliers.lean.
4. Verify raw H1 targets arise from the actual stored V and its directional derivatives,
   and raw H2 target is V(R,R^-1 X R)-V(I,X). Do not assume these new facts as published inputs.
   Potential data and source formulas are in data/source/m12_problem.py and polynomial JSON.
   A useful integer scaling: H1 uses 3*D_V; boundary substitution can use 16*D_V because
   V has degree 4 and the rotated coordinates have denominator 2.
5. Connect the polynomial differential inequalities to the actual Lipschitz control path
   (a.e. derivatives), using the already proved convex-combination and integration lemmas.
   Prove the potential along the path is absolutely continuous from its smoothness and
   path Lipschitz regularity; do not silently impose C1 regularity on the trajectory.
6. State published geometric dependencies precisely, including why the path lies in the
   exact region used by the certificate. Check whether numerical confinement refinements
   require additional elementary proofs. Do not hide an unverified new inequality here.
7. Assemble final conditional density theorem; complete clean portable build instructions,
   source provenance and axiom audit. Root Certificate.lean and a clean lake build still
   need to be completed; only the cached direct Lean build has been exercised.

## Practical details

- Lean v4.33.0, mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
- Existing read-only cache is the Courtade-Kumar publish project; wrapper sets LEAN_PATH.
- .lake/build/lib/lean is a symlink overlay of cached mathlib, plus locally compiled missing
  modules. scripts/ensure_cached_module.py compiles missing dependencies without touching cache.
- Use /usr/local/bin/python3.12 for NumPy/SymPy exporters. Plain python3 is fine for build scripts.
- Always set the real workdir explicitly; the old default cwd is nonexistent.
- Generated GramData uses upper-triangle storage and reflection by definition. Original
  exported matrices are exactly symmetric (checked in Python); original 104 benchmark
  also proved full-list symmetry in Lean.
- Matrix proof reports include only [propext, Classical.choice, Quot.sound]. An error log
  containing sorryAx is a failed attempt and must never be counted as a proof.
- Do not rerun old experiments: monolithic Benchmark.lean, SymmetryProbe.lean,
  BenchmarkFirstRowCbv.lean. Working row checks use ordinary `decide +kernel` and
  the proved list-dot-product equivalence; the proof-producing cbv probe was abandoned.

## Latest verified additions and current work

All four quotient/reduction checks have now passed with the structurally recursive checker.
All 75 multiplier certificates passed (`logs/multipliers_verified.json` stores source hash).
PolynomialDerivative, PolynomialSubstitution, PolynomialRegularity and GeometricCoordinates
have compiled and their audited theorems use only standard axioms. The latter proves
X^2=-I and the exact boundary conjugation coordinates. No C1 assumption was added to
control paths: absolute continuity of polynomial evaluations is proved directly.

New source (not yet all verified):
- scripts/emit_sos_assembly.py -> Certificate/Assembly: connects each multiplier and PSD
  proof to its Gram expansion, then checks the total SOS sum. The first H2 block assembly
  is being compiled (session 49488, logs/assembly_H2B000.log).
- scripts/build_sos_assembly.py: imported-olean/source hash and axiom reports.
- scripts/emit_potential_checks.py -> Certificate/Potential: actual V, degree4 bound,
  symbolic derivatives and scaled substitutions, plus four checks against raw targets.
- Certificate/Potential/Semantics.lean: drafted connection to actual boundary coordinates
  and analytic regularity; still requires compilation.
- Session 15154: DirectionalPolynomial, Potential/Data, Potential/Semantics, then Potential/H2;
  logs named directional_polynomial, potential_data, potential_semantics, potential_H2.
- Session 70000: priority H2 matrix batch (resume enabled), logs/matrices_H2_priority.log.
- Session 72549 still checks H2 SOS expansions. Other matrix workers continue; inspect
  process/log state before resuming. No failed/empty logs should be counted as proofs.

Confinement audit: M14/report.md sections7–8 explicitly derive the height cap and g norm/sector
constraints. hv5_certify_replay.py proves numeric refinements in Python exact arithmetic,
including 2*cosh(c8/3)<16/5, but these are NOT yet Lean verified. Published confinement alone
must not be silently assumed to contain all these new deductions.

## Implementation efficiency review

The monolithic 104-by-104 SOS expansion benchmark was interrupted after more than
16 minutes without a verified result. This is distinct from the already verified
104-by-104 PSD benchmark. Certificate/FastExpansion.lean has compiled and its
soundness theorem has only standard axioms: it merges entry polynomials and rows
without repeatedly flattening and re-sorting individual terms. H1 expansion
sources now use it, but no representative H1 timing has yet established a speedup.
The next performance comparison should use a 34-by-34 block before the 104-by-104
block, and distinguish compiler time from time waiting for the single compiler slot.

Candidate follow-ups (not implemented or verified): row/chunk witnesses for large
expansions; upper-triangle-only expansion with a proved symmetry lemma; shared
residual/dot-product witnesses for PSD checks. Each needs a soundness proof and
benchmark, rather than assuming generated arithmetic is trustworthy.

The temporary bulk compilation pause marker was removed following this review.
Existing workers may continue; do not start duplicate batches. The default
single-compiler gate remains to limit memory pressure. Potential/H1_0 and the
FastExpansion foundation have compiled; the remaining potential semantic and
assembly modules require their own successful checks. This is not a completed
certificate or unconditional packing theorem.

## Workflow optimization implementation

New kernel-proved foundations: MergeArithmetic (single-merge equality and sorted
translated multiplication), SparseExpansion (drop zero coefficients before merging),
and ChunkedExpansion (independent row witnesses joined by checked binary merges).
All have successful standard-axiom audits. The checker soundness does not depend on
trusting sortedness or Python generation. No source certificate coefficients changed.

Representative H1_0 block1,34x34, single compiler,8GB cap: original Gram expansion
10.6126s; zero-filtered/direct-merge expansion4.3453s (2.44x, one comparison, excluding
queue). At4GB the original/row-merge/direct-merge variants exceeded the cap; the
zero-filtered version succeeded in4.8833s. The chunked alternative also verified
this block, but took19.10s across two modules; it is therefore not the default for
ordinary blocks.104x104 comparison is still running and must be reported separately.

scripts/emit_sos_checks.py now selects SparseExpansion+MergeArithmetic for H1 blocks
with nonzero index; H2 and the three104x104 blocks are unchanged pending benchmarks.
Generation preserves timestamps when source bytes are unchanged. Builder/status hashes
include the new checker sources. The full generated production proof is being checked,
not merely the isolated benchmark assertion.

The build wrapper now provides conservative content/dependency caching, output locks,
priority/FIFO admission, explicit compiler-only timeouts, and separate queue/compiler
measurements. Eleven focused tests passed. Real DiagonalCheck cache hits reused a
previous2.0975s compilation with no compiler launch (about1.3-1.6ms inside wrapper,
excluding Python startup). Legacy dependencies require provenance bootstrap before
cache hits are allowed; the shared data dependency chain is being bootstrapped.

Bulk batches remain temporarily gated during representative benchmarks; remove
logs/pause_data_builds before resuming them. One temporary second compiler slot was
used only for small development checks while an older H1_2 job completed. Benchmarks
now use the default one compiler. Full packing theorem remains unverified.

## Optimization validation completed

Selected production implementation: sparse/direct-merge checks for ordinary H1 blocks,
shorter-outer-factor multiplication for H1, and128-check chunk modules for the three
104x104 blocks. H2 proof sources remain unchanged. The generator emits all required
chunk dependencies and builder/status source hashes include them and the new foundations.

Verified H1_0B000 full Gram expansion:211.8312s compiler time, standard axioms only.
Both monolithic104 variants exceeded180s; no direct speed ratio is claimed. The complete
weighted theorem and its assembly with actual PSD/multiplier proofs also passed. Reuse
of the completed six-stage block through build_sos_checks took0.3259s,6 cache hits,
0 compiler seconds. Updated production proofs also passed H1_0B001,H1_1B043,H1_2B043;
B043 is the largest ordinary multiplier product (320x16 terms before merging).
Multiplication improvements: H1_0B0008.64→4.80s; H1_1B04310.85→6.56s. Retained
`decide +kernel`: rfl probes were slower. Thirteen workflow tests passed; regeneration
left all505 relevant Lean source bytes and timestamps unchanged.

All five potential semantic bridge modules now compile with only standard axioms.
An abstract three-entry selector lemma replaced expensive reduction of the255-term
potential. No new axioms/sorry/native_decide were introduced. The geometric confinement
bridge still needs explicit treatment, including the C1/AC regularity distinction in M14.

At final validation:129/248 PSD matrices,11/248 complete Gram/multiplier expansions,
4/4 quotient reductions,75/75 multiplier certificates. These counts exclude newly
queued work and do not establish the full packing theorem. The final status command
is the authoritative count of current-source reports.

Bulk pause removed. Existing matrix/H2 workers resumed; a single new full optimized
SOS worker was started with resume enabled,8GB cap,240s per-module compile timeout,
and bulk priority. Check logs/optimized_sos_all.log before launching another worker.

Post-resume smoke: optimized SOS blocks H1_0B002 and B003 passed in8.24s and8.86s
compiler time, respectively. Existing batches are progressing with the pause removed.
Matrix reports now also capture compiler/queue/cache metrics; unchanged H2B009
rechecked via2 cache hits in0.070s, with0 compiler time. Older already-running matrix
controllers retain their old report schema until exit; their wrapper logs still record
new timing details. No stale verification reports were found by status.py.

## Completed component batches (2026-10-27 status check)

All248/248 matrix-positivity proofs and248/248 Gram/weighted expansion checks
have passed for the current source hashes, alongside75/75 multiplier certificates
and4/4 polynomial reductions. No batch workers remained when this was checked.
These are component counts, not a verified aggregate certificate or density theorem.

Started the H2 assembly next. Its dependency check rejected an older compiled
SOS artifact whose source timestamp was newer. Refreshing the23 H2 expansion
artifacts through the provenance-aware wrapper before retrying assembly. This
is a build-provenance issue; no mathematical check has failed in this step.
Aggregate identities, the final control theorem, and geometric confinement still
require their own successful checks.

The H2 artifact refresh completed successfully; its23-block assembly check is now
running. Potential/H2.semantic_identity also compiled successfully (5.891s compiler
time), using only propext, Classical.choice, and Quot.sound. This verifies the
boundary target's exact relationship to the stored potential.

## Assembly continuation (2026-10-27)

H2's complete target_lower_bound has now passed. Fixed two generator defects:
the list membership split left a final empty-list case, and the determinant
generator evaluations needed to unfold their small `_0` data definitions.
Generation now preserves unchanged assembly files.

The monolithic H1_0 sum exceeded a240s compiler timeout. Replaced the H1 sums
with74 separately checked exact merges per identity, grouped eight per module
under Assembly/SumTrees. Python proposes intermediate polynomials; Lean checks
each merge and the final recorded SOS equality. No coefficients were changed.
The H1_0 tree is complete; H1_1/H1_2 are building. Session37623 is the dedicated
tree builder. The original sum experiment's log is H1_0Sum_early.log.

For assembly speed,25 small block proofs now share a module. The75 H1_0 block
assemblies compiled in6.04+5.88+8.60 seconds, excluding queue time. Their theorem
names and statements are unchanged. The aggregate proof imports only these
bundles, not the duplicate legacy per-block modules. Session74286 builds all
three H1 assemblies with the new pipeline. The superseded per-block controller
(PID87585) was stopped after sandbox approval; its completed outputs remain.

TrajectoryCost.control_cost_of_certificate_on_path passed (2.326s compiler):
the actual stored potential is integrated along an absolutely continuous path.
ControlTheorem now specializes this structural theorem to the actual four
certificate inequalities. RegionSanity.circleInitial_region also passed,
showing that all19 primitive constraints and determinant relations are jointly
satisfiable. The final actual-ODE path structure and conditional density theorem
are drafted in Certificate/Final.lean, but NOT YET CHECKED.

scripts/verify_certificate.py will build the final modules, audit all named final
theorems, and record their full local source/artifact dependency manifest. The
report deliberately distinguishes an on-region/conditional theorem from an
unconditional packing theorem. M14's new confinement deductions remain outside
the currently verified chain and must not be described as published assumptions.

Fixed bootstrap planning for not-yet-built local dependencies, without weakening
normal build dependency checks; all14 focused cache tests pass. The root
Certificate.lean now imports Final. No standalone clean Lake build has yet run.

All four assembled identities now pass, and all248 block assemblies are accounted
for by the H1 bundles and the23 H2 modules. Both tree and assembly workers exited0.
The final certificate conversions were split into Definitions, Vertex0/1/2 and
Boundary modules so they can be checked independently. Avoid `change` through
the evaluation of the large potential: an explicit selector equality and congrArg
transport keeps the polynomial opaque. Likewise use an explicit mul_pos argument
instead of positivity, which explored the enormous local polynomial hypotheses.
Vertex0 and Boundary passed, and the final driver has since also passed Vertex1.

The first final-driver attempt redundantly replayed the old Potential/H1_1 target
identity and hit a180s timeout. Its successful earlier artifact (02:48 on Oct27)
and original successful axiom log remain intact, and its source is unchanged.
The default final driver now reuses completed component builds, as intended;
--rebuild-local is the explicit full replay path and should allow longer timeouts
for those older checks. This is not an arithmetic counterexample or a new premise.

Current final driver: session13328, logs/final_verification_driver.log. It will
write logs/final/verification.json only after all final checks pass. Original
input hashes10/10 and exact-certificate hashes4/4 match. The final manifest now
also covers .olean.private/.olean.server companions. README was rewritten to
explain the theorem's exact assumptions and still marks the final audit pending;
update that status only once the driver succeeds.

## Final conditional theorem verified

Session13328 exited0. All12 final-stage modules, including Certificate/Final.lean
and root Certificate.lean, compiled successfully. The six audited final theorems
depend only on propext, Classical.choice, and Quot.sound. In particular,
AdmissibleTrajectory.cost_lower_bound derives gamma from the actual fixed SOS
certificate and original matrix ODE, and density_bound_of_admissible_trajectory
proves8950112/10000000<density from the explicit geometric cost comparison.
The certificate inequalities are conclusions, not premises of that final theorem.

The report records hashes for the complete local Lean dependency closure, compiled
outputs and their companions, compiler, configuration, and original input manifests.
It explicitly records unconditional_packing_density_theorem_verified=false.
Further work toward that stronger target must supply packing/control correspondence
and actual confinement; M14's extra confinement deductions have not been formalized.
No claim is made that the separate clean standalone Lake replay has been performed.

## New confinement deductions completed (2026-10-27)

The next continuation closed the additional confinement obligations of the new
certificate argument. Eleven `Confinement*.lean` modules were added. No search for
a new certificate or optimization was run.

- `ConfinementRho` bounds the sum of the three star coordinates by 83/20 using
  rational inequalities and a six-case ordering argument. This proves the required
  height bound directly, without a numerical maximizer.
- `ConfinementState` derives all twelve X-dependent primitive constraints.
- `ConfinementDomain` proves equivalence of the six rho inequalities with the
  original cusp/wall inequalities in the three rotated charts. The unrotated chart
  is explicitly x=a/(p+h), y=1/(p+h), with y<=9/2 and y<=15(sqrt(3)/3-x).
- `ConfinementPolar` constructs a continuous angle by integrating angular velocity;
  normalized-row differentiation and constant rotated coordinates prove the
  sine/cosine representation. No winding-number premise is introduced.
- `ConfinementSector` uses nonnegative angular velocity, the endpoint, and total
  cost to prove the sector inequalities. `ConfinementGroupPath` checks the two
  conjugated paths and derives all six sector inequalities.
- `ConfinementEnergy` and `ConfinementMatrixNorm` give a simpler substitute for
  the hyperbolic-length/cosh argument: E=(g11-g22)^2+(g12+g21)^2 has zero values
  at both endpoints, and its differential bound implies E<=6/5 for cost<=3.11.
  The square-root regularization is the exact rational 1/100000000; no limit or
  floating-point approximation is used.
- `ConfinementRegularity` and `ConfinementFromAC` derive interior derivatives
  from the AC and a.e. matrix equation already used by the original path theorem.
- `ConfinementFinal` proves gamma<3.11, derives all nineteen constraints in the
  low-cost case, and handles higher-cost paths directly. Thus the new final
  `CompactTrajectory.cost_lower_bound` has neither a certificate-region premise
  nor an upper-cost premise. `density_bound_of_compact_trajectory` gives the
  same exact decimal density bound with the published density comparison.

Every new module and the stronger final theorems passed Lean, using only
propext, Classical.choice, and Quot.sound. The reproducibility driver was extended
to eighteen theorem audits and the new complete dependency closure; see
`logs/final_verification_with_confinement.log` and `logs/final/verification.json`
for the final run. Root `Certificate.lean` now imports `ConfinementFinal`.

The completed scope is the new certificate/control argument relative to the
published geometric inputs. Existence and reduction of the minimizing body,
the published HV compact-domain theorem itself, and the geometric density/cost
comparison remain explicit hypotheses. Fable's numerical replay of the published
HV compactness theorem is not part of this Lean proof. These facts must remain
visible when describing what was formalized; the result is not an unconditional
formal packing theorem.

The final confinement verification driver exited 0: all 23 final build stages
passed, all 18 named theorem audits use only the standard axioms, and the manifest
covers 1,137 local dependency modules. A separate source scan of all 1,411 local
Lean files found no proof placeholders, `native_decide`, or custom axiom declarations.
`scripts/status.py` confirms 248/248 matrix proofs, expansions and block assemblies,
75/75 multipliers, 4/4 reductions and assembled identities, the conditional density
theorem, and the new confinement deductions. No stale component reports remain.
The unconditional packing-theorem flag remains false, deliberately and accurately.

## Geometric bridge continuation (2026-10-27)

New proof modules:

- `PackingDefinitions`: copies the original benchmark definitions exactly, inside
  `Certificate.Packing`, without importing its unproved conjecture.
- `PackingLattice`: adapts and rechecks the recovered $100-run lattice argument.
  Uses the general scaling law for ball volume, so no explicit pi formula or
  additional special-function dependency is needed.
- `PackingHexagon`: proves interior-disjoint lattice translates from the three
  supporting strips and vertex conditions of a circumscribed hexagon.
- `PackingGeometry`: two consecutive normalized side midpoints imply covolume
  `2*sqrt(3)`; combines this with the actual packing-density comparison.
- `CompactExclusion`: avoids the published numerical interval grid. Outside the
  compact domain, the scalar area bound is at least `269/300`, and Lean verifies
  `gamma/(2*sqrt(3)) < 269/300`. This is the weaker exclusion sufficient here,
  not a proof of the original stronger octagon-comparison statement.
- `AreaControlledTrajectory`: splits on that threshold and derives compactness
  only in the case that needs the certificate.
- `CurvatureControl`: normalizes three nonnegative curvature forms, proves their
  sum is positive, reconstructs `Z(u)`, and proves the precise `X` equation.
- `CurvatureTrajectory`: obtains coordinate derivatives a.e. from AC regularity;
  differentiates determinant one on the interval interior (endpoints are null);
  chooses simplex controls with a harmless default on the exceptional set;
  derives the full eight-coordinate ODE. Cost integrability is derived too.
- `PackingFinal`: concludes the decimal bound for the original packing density
  from either the normalized control data or the curvature data.

Only one additional pinned mathlib module was needed:
`Mathlib.Analysis.Convex.Measure`, built in the local overlay, with its source
copied into `vendor_mathlib`. The external cache was left unchanged.
`data/geometric_provenance.json` records original source hashes and the exact
packing-definition body hash; the verifier checks the latter.

The next substantive obligations are geometric, not further certificate assembly:
prove the HV area estimate (Theorem 5.0.6) from a minimal circumscribed hexagon,
and construct the normalized balanced-boundary data for a minimizer, including
its area identity and comparison with arbitrary bodies. No such existence or
area theorem has been silently added as an axiom.

Important for the remaining transfer: the published minimizer is for lattice
density (equivalently the minimum-circumscribed-hexagon ratio). Do not infer
an affine-invariance theorem for the original unrestricted-isometry packing
density from this work. The verified construction gives a lower bound from
one lattice; it does not prove that all optimal packings are lattices. Transfer
the normalized area/hexagon-ratio lower bound to each body's lattice candidate,
then use `packingDensity_ge_hexagon`. This avoids needing Rogers/Fejes Toth's
full equality of general and lattice packing density.

Published sections still needed: HV 2.2 and 2.4 for minimizer existence,
regularity, midpoint-hexagon and balanced-boundary construction; 3.1--3.2 for
the frame/time normalization and the geometric area integral; 5.0.6 for the
extra-contact-point area estimate. The algebraic control reconstruction and
the numerical exclusion formerly taken from 3.3--3.6 and 5.0.2 are now local
proofs. The geometry must be instantiated on actual bodies, not replaced by
an existence hypothesis that merely restates the target packing bound.

Verification workflow: the default final-stage replay timed out after 180 seconds
on the unchanged `NewCertificateVertex1` proof. This is a resource timeout, not a
Lean proof error. A hash comparison found all 1,136 old dependency sources and
artifacts (excluding the changed root import) identical to the prior successful
verification. That report is archived as
`logs/final/verification_before_geometric_bridge.json`; comparison evidence is in
`logs/prior_certificate_integrity.json`.

The new `verify_certificate.py --audit-built` mode rebuilds the root and checks
all 32 named theorem axioms in one importing module, while the normal wrapper
rejects stale local imports. All new/changed modules must be compiled first.
It records `build_mode=audit-built` in the final manifest. This avoids repeating
expensive unchanged proofs; it does not add mathematical assumptions or use a
non-kernel decision procedure. The ordinary final-stage and full replay modes
remain available.

Final geometric-bridge audit passed. Both the root build and the fresh 32-theorem
axiom audit exited successfully. The manifest records 1146 local dependency modules
and only `propext`, `Classical.choice`, and `Quot.sound`. `scripts/status.py`
confirms all finite certificate component counts unchanged and all three new
bridge flags true. The source scan of 1420 local Lean files found no unfinished
proof placeholders, `native_decide`, or custom axioms. The unconditional packing
theorem flag remains false. Final records: `logs/final/verification.json`,
`logs/final_geometric_audit.log`, and `logs/geometric_bridge_status.json`.

## Published geometric ingredients: triangle areas and the corner-cut argument

Added eight modules, imported by the project root:

- `TriangleArea`: exact Lebesgue area of arbitrary and degenerate triangles.
  Segment nullity and the initial triangle-containment lemmas are adapted from
  the recovered Fable lattice reduction; the exact area proof partitions a
  parallelogram into a triangle and its reflection and proves the overlap null.
- `ParallelCutArea`: HV Lemma 5.0.5, for an arbitrary planar triangle. Scaling
  from a corner gives the square-area factor; a point anywhere on the parallel
  line gives the claimed square-root formula. All areas are actual measures.
- `CornerCut`: explicit competing hexagon in a square, including all strip and
  vertex conditions required by `Hex`, its covolume, and the compactness/contact
  argument for covolume minimality.
- `CutHexagonArea`: proves that this competitor also has geometric area
  `4-d*e`. The square is decomposed into the competitor and the two opposite
  corner triangles. Boundary overlaps are proved null, and the triangles are
  proved disjoint. Thus no unproved area/covolume identification is used in
  the geometric-minimality version of the contact theorem.
- `HVCornerArea`: compactness makes a missing contact into a strict gap, which
  gives a strictly smaller circumscribed hexagon and contradicts minimality.
  Convexity produces a point on the precise parallel cut. The returned point
  belongs to K and to the correct corner triangle; the extra triangle is
  contained in K and has the published square-root area contribution.
  `HexAreaLowerBound` compares ENNReal measures, avoiding the pitfall that an
  infinite measure would become zero under `toReal`. Conversion to real area
  is performed only for the explicit competitor, whose measure is finite.
- `HVTriangleGeometry`: HV Lemma 5.0.4 in explicit circle-representation
  coordinates. Checks the three midpoint equations, six edge-incidence
  equations for the exterior vertices, six Lebesgue triangle-area formulas,
  and the interior-area sum. The hypotheses on the star parameters are
  nonnegativity and `u*v+v*w+w*u=1` where needed.
- `HVAreaExpression`: identifies the actual geometric expression in 5.0.6,
  normalized by `2*sqrt(3)`, with the existing `areaScore` exactly. This checks
  the square-root penalties, factors of two, and cyclic indexing.
- `RegularHexagonArea`: constructs the inscribed hexagon as six triangles,
  proves pairwise intersections null using separating linear forms, computes
  area `3*sqrt(3)/2`, and proves the baseline bound for every compact convex
  body containing the six points. No polygon-area or overlap hypothesis is
  assumed.

Scope remains incomplete. The single-corner theorem is in square coordinates.
It must still be transported to each critical-hexagon corner; the extra caps
must be assembled with the baseline hexagon without double-counting. These
steps are needed to prove HV 5.0.6 itself and discharge `HasAreaEstimate`.
The minimizing balanced disc, boundary regularity/normalization, area identity,
and comparison with arbitrary bodies are also not yet constructed. The final
packing theorem's assumptions have not been silently removed or replaced by
axioms. Its unconditional-verification flag remains false.

`data/published_geometry_provenance.json` records the local paper's hash,
precise proved components, and remaining obligations. The final verifier now
always runs a dedicated importing axiom audit (also in its ordinary/full-replay
modes), covering 47 named results. `--audit-built` continues to reuse the
unchanged expensive certificate artifacts while checking dependency freshness.
The previous 32-theorem audit is preserved in
`logs/final/verification_before_published_geometry.json`.

Final verification of this phase passed: root import and fresh 47-theorem axiom
audit both exited successfully. The manifest contains 1,154 local dependency
modules and only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
All 1,145 prior dependency source/artifact pairs are unchanged. The source scan
covers 1,428 local Lean files, with no unfinished-proof markers, `native_decide`,
or custom axioms. Status checks retain 248/248 matrices and Gram expansions,
75/75 multipliers, and 4/4 reductions and assembled identities, with no stale
reports. The full-HV-area and unconditional-density flags are both false.
Evidence: `logs/final/verification.json`, `logs/final_published_geometry_audit.log`,
`logs/published_geometry_status.json`, `logs/published_geometry_source_scan.json`,
and `logs/published_geometry_prior_integrity.json`.


## Completing the geometric area dependency (2026-10-27)

The full normalized HV Theorem 5.0.6 is now proved for the strict star domain
used in the paper. This phase closes the missing contact transport and area
assembly, rather than taking them as new assumptions.

- `AreaAssemblyHelpers`: triangle half-plane containment and nullity of any
  affine level line of a nonzero linear functional.
- `HVCornerRegions`: the six explicit exterior sectors. Every pairwise overlap
  is null, as is each sector's intersection with the inscribed hexagon.
- `HVAreaAssembly`: all normalized corner vertices are in their sectors;
  compact corner pieces add to the baseline area without double-counting.
  The resulting six-contact theorem has no assumed disjointness premise.
- `HexagonLinearTransport`: transports actual `Hex` objects, their measured
  areas, and geometric minimality under invertible linear maps. Triangle
  images and areas are transported with the exact determinant factor.
- `HVCornerCoordinates`: the explicit square-coordinate map, its determinant,
  adjacent midpoint and vertex images, and the critical area normalization.
- `HVFirstCorner`: the first contact contribution in the original normalized
  hexagon. Active corners use the square theorem; inactive corners contribute
  zero. The returned point belongs to both the body and its corner triangle.
- `HVRotation`: the minus-sixty-degree map, cyclic parameter permutation,
  all supporting-strip identities, and preservation of actual area.
- `HVAreaBound`: the other two contacts follow by rotation. Central symmetry
  gives the opposite contacts. The checked six-piece assembly proves
  `areaScore u v w <= area(K)/(2*sqrt(3))` from geometric minimality.
- `NormalizedHexagon`: constructs the circumscribed hexagon itself, checks all
  nine side/vertex conditions, computes its packing lattice covolume, and
  pulls that lattice back to the original body. It does not assume affine
  invariance of the original arbitrary-isometry packing density.
- `PackingFromCriticalHexagons`: derives `HasAreaEstimate` from an explicit
  critical-hexagon family and the area identity. The new highest-level packing
  theorem takes this presentation and a curvature trajectory; it does not ask
  separately for the area bound or a packing hexagon.

The strict inequalities `u,v,w > 0` match HV's open star domain (Corollary
3.1.6 and Theorem 5.0.6). No claim is made about degenerate star triples.
All new proofs use the original actual Lebesgue area and packing definitions.

The remaining work is still substantial geometric construction, not certificate
arithmetic: HV Chapter 2's minimizing lattice-density/minimum-hexagon body;
its balanced multicurve and regularity (especially Lemmas 2.2.5–2.2.7 and
2.4.2–2.4.6); the normalized frame, strict star conditions, and endpoints;
and Section 3.2's area identity from the boundary integral. The pinned mathlib
search did not find a ready-made general Green's-theorem area formula for this
boundary presentation. These results have not been asserted or replaced by
axioms, and `unconditional_packing_density_theorem_verified` stays false.

The prior 47-theorem verification is preserved in
`logs/final/verification_before_full_hv_area.json`. Final verification details
for this phase are appended below once the importing axiom audit finishes.

`NormalizedHexagonArea` additionally closes the actual area normalization.
After a cyclic permutation makes the middle parameter minimal, a reflected
linear map identifies the hexagon with a measured cut hexagon. The exact
Jacobian gives Lebesgue area `2*sqrt(3)` for all strictly positive star triples.
The result `hales_vajjha_area_bound_of_minimal_hexagon` takes ordinary minimality
of this explicit geometric hexagon, without assuming its area equals its
covolume. This adds three named audits, bringing this phase's total to 71.

Final importing verification passed for all 71 named theorems, with only
`propext`, `Classical.choice`, and `Quot.sound`. The manifest now covers
1165 local dependency modules. The full-HV-area and
critical-family-area-estimate flags are true; the unconditional density flag
remains false. All 1,153 prior dependency source/artifact/companion sets are
unchanged, excluding the intentionally extended root. The source scan covers
1,439 local Lean files and finds no unfinished-proof markers, custom axioms,
or `native_decide`. Evidence: `logs/final/verification.json`,
`logs/final_full_hv_area_audit.log`, `logs/full_hv_area_prior_integrity.json`,
`logs/full_hv_area_source_scan.json`, and `logs/full_hv_area_status.json`.

## Boundary area identity from geometric arcs

The continuation closes the area identity of HV Section 3.2 without importing
Green's theorem as an assumption. Five modules connect actual Lebesgue area to
the control cost:

- `RadialSectorArea` parametrizes a sector by `(r,t) ↦ r • γ(t)`. Its derivative
  and determinant are checked, giving Jacobian `r * det(γ,γ')`. The convex
  body's gauge proves injectivity from boundary membership and arc injectivity.
  The pinned mathlib change-of-variables and product-integration theorems give
  sector area `1/2 * integral |det(γ,γ')|`.
- `BoundaryArcArea` assembles any finite family of boundary arcs. Their sectors
  are disjoint when the arc interiors are disjoint. Boundary coverage implies
  that they fill the convex body except for its frontier and the finitely many
  rays through arc endpoints. All omitted sets have zero planar measure.
- `FrameBoundaryCalculus` derives the six arc derivatives from the original
  AC coordinates and a.e. group ODE. It proves the determinant integrands are
  nonnegative in the star domain and their sum is `6h`.
- `FrameBoundaryArea` proves `FrameBoundary.cost_eq_area`. Its only new inputs
  are geometric: the six frame arcs lie on the frontier, cover it, and have
  injective, disjoint interiors. Neither derivatives nor area are extra fields.
- `PackingFromBoundary` feeds this theorem into the existing HV area estimate
  and density theorem. `BoundaryCriticalHexagonFamily` has no cost/area field.
  The new curvature-based final theorem also retains the previously proved
  reconstruction of the controls.

The numerical certificate and prior geometric modules are unchanged. Remaining
dependencies are minimizing-body existence/comparison and construction of its
normalized balanced boundary and critical-hexagon presentation, including the
coverage/nonoverlap properties. These are not asserted automatically for every
disc. The unconditional packing theorem remains false in the status report.

The prior 71-theorem audit is preserved in
`logs/final/verification_before_boundary_area.json`. This phase adds 13 named
checks to the importing audit, for 84 in total. Final audit evidence is recorded
below after the importing build finishes.

Final verification passed: all 84 named theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. The manifest covers 1,170 local dependency
modules. All 1,164 prior dependency modules, excluding the extended root,
retain their source, artifact, and companion hashes. The 1,444-file local Lean
source scan has no unfinished-proof markers, custom axioms, or `native_decide`.
The boundary-area and frame-area flags are true; the unconditional packing
flag stays false. Evidence: `logs/final/verification.json`,
`logs/final_boundary_area_audit.log`, `logs/boundary_area_prior_integrity.json`,
`logs/boundary_area_source_scan.json`, and `logs/boundary_area_status.json`.

## Supporting geometry from the convex boundary

The next continuation derives geometric fields that previously had to be
supplied as a `BoundaryCriticalHexagonFamily`.

`ConvexBoundarySupport` separates a boundary point from the convex interior
by a continuous linear functional. Its value along the boundary arc has a
local maximum, so its derivative vanishes. A checked two-dimensional
determinant identity then shows that the entire body lies on the correct side
of the oriented tangent. This uses the pinned mathlib separation and Fermat
theorems, not a new supporting-line assumption.

`StateLinearFrame` constructs the determinant-one linear equivalence from the
state matrix. Its inverse preserves area, and boundary membership gives the
three normalized contact points. `TangentHexagonSides` identifies the tangent
normal forms with the explicit hexagon sides. `FrameBoundarySupport` derives
all enclosing strips from these facts and central symmetry. The supporting
inequalities extend to the endpoints by continuity of the state coordinates.

`FrameBoundaryStar` treats the equality cases in the weak star conditions.
At an interior time, a zero star coordinate places two adjacent boundary
points on the same supporting tangent. Applying Fermat's theorem along the
second boundary arc forces their tangents to be parallel. Their determinant,
however, is the fixed nonzero adjacent-root determinant because both `g` and
`X` have determinant one. This proves strict interior stars. Strictness at
the two endpoints is not claimed or needed.

`PackingFromFrameBoundary` constructs the former geometric family when strict
stars on the closed interval are supplied. The stronger final interface in
`PackingFromConvexBoundary` removes that strict-star input: it proves the HV
area estimate in the interior and extends the scalar inequality to endpoints
by continuity. An interior time supplies the explicit packing hexagon.

The strongest theorem is
`packing_density_bound_of_curvature_convex_boundary`. Its remaining inputs
are the symmetric convex disc, a normalized curvature trajectory, its six
arcs forming the boundary once, and `HexAreaLowerBound K (2*sqrt(3))`.
The trajectory still includes weak star inequalities, AC regularity,
determinant/ODE constraints, nonnegative curvature, and normalized endpoints.
The existence of such a normalized presentation, its minimum-hexagon property,
and minimizing-body existence/comparison are still unproved. The unconditional
flag remains false.

This phase adds 21 named audits, bringing the total to 105. The preceding
84-theorem report is preserved in
`logs/final/verification_before_boundary_support.json`. Final importing-audit
results are appended after the build completes.

Final verification passed: all 105 named theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. The manifest covers 1,177 local dependency
modules. The 1,169 prior dependency modules, excluding the changed root, retain
their source, artifact, and companion hashes. All seven new modules compiled,
followed by the root and a fresh importing axiom audit. The 1,451-file local
Lean source scan has no unfinished-proof markers, custom axioms, or
`native_decide`. Supporting-hexagon and strict-interior-star verification flags
are true; the unconditional packing flag remains false. Evidence:
`logs/final/verification.json`, `logs/final_boundary_support_audit.log`,
`logs/boundary_support_prior_integrity.json`, and
`logs/boundary_support_source_scan.json`.

The independent current-source status pass also succeeds, retaining all 248
matrix proofs, 248 Gram expansions, 75 multipliers, four reductions, 248 assembled
blocks, and four complete identities. No component report is stale. See
`logs/boundary_support_status.json`.

## Curvature from convexity

This continuation formalizes the curvature-sign step of HV Lemma 2.4.6 and
removes nonnegative curvature as a separate input to the strongest density
theorem.

`ConvexBoundaryCurvature` first proves a scalar necessary second-derivative
condition for a local minimum. If the second derivative were negative, the
pinned mathlib second-derivative test would give a local maximum as well. The
function would then be locally constant, contradicting that second derivative.
Applying this to signed distance from the convex supporting tangent gives
`det(velocity, acceleration) >= 0`. The tangent need only be differentiable at
the point under consideration; continuous curvature is not assumed.

`FrameTrajectory` retains the AC frame coordinates, determinant constraints,
weak star inequalities, group ODE, and normalized endpoints. It deliberately
has no curvature or control field. `FrameTrace` states boundary membership,
coverage, and injectivity/nonoverlap. The group ODE is upgraded to pointwise
interior derivatives using the already checked AC fundamental-theorem argument;
AC also gives the state-coordinate derivatives almost everywhere.

`FrameAcceleration` differentiates the actual vector `g(t) X(t) v`. The group
ODE and `X^2 = -I` identify its derivative with `g(t) (X'(t)-I) v`. The
area-preserving frame identifies its signed curvature with the exact matrix
expression used in the certificate's curvature-to-control reconstruction.
`FrameTrace.curvature_nonneg_ae` applies the convex-boundary lemma to the three
control directions. The null endpoints require no second-derivative claim.

`packing_density_bound_of_convex_frame` now builds the former curvature
trajectory from these results and concludes the strict 0.8950112 bound. The
remaining geometric inputs are minimizing-body existence/comparison and the
construction of its normalized frame boundary with the minimum-hexagon
property. Weak star inequalities, AC regularity, determinant/ODE constraints,
and endpoints are still explicit presentation hypotheses. Neither minimizer
existence nor a normalized boundary is asserted automatically for every disc.

The nine additional named audit entries bring the total to 114. The preceding
105-theorem report is preserved in
`logs/final/verification_before_convex_curvature.json`. All 1,176 previous
non-root dependency modules retain their audited source/artifact/companion
hashes (`logs/convex_curvature_prior_integrity.json`). The 1,455-file local Lean
source scan found no unfinished-proof markers, custom axioms, or `native_decide`
(`logs/convex_curvature_source_scan.json`). Final importing-audit evidence is
recorded below after completion.

Final verification passed. All 114 named theorem audits use only `propext`,
`Classical.choice`, and `Quot.sound`; the import manifest covers 1,181 local
modules. The independent current-source status pass preserves all 248 matrix
proofs, 248 Gram expansions, 75 multipliers, four reductions, 248 assembled
blocks, and four complete identities, with no stale component reports. The
curvature-from-convex-boundary flag is true; the unconditional density flag is
false. Evidence: `logs/final/verification.json`,
`logs/final_convex_curvature_audit.log`, and `logs/convex_curvature_status.json`.


## Constructing a ratio-minimizing body and radial boundary

This continuation proves existence instead of adding a minimizing-body input.
A maximal determinant pair normalizes each symmetric convex disc between the
coordinate diamond and square. The normalized family is compact in the
Vietoris/Hausdorff topology; the diamond retains a fixed inner ball. Nearby-body
dilation inclusions control actual area and the circumscribed-hexagon infimum.
Their ratio is lower semicontinuous and attains a global minimum.

`criticalHexArea` is a genuine infimum of actual Lebesgue hexagon areas. Its
positivity, finiteness, monotonicity, and exact affine covariance are proved.
Scalar dilation gives a ratio minimizer with infimum exactly `2*sqrt(3)` and
area minimality among all discs satisfying this hexagon-area lower bound.
There is no claim here that the infimum is attained by a hexagon, or that this
objective has been identified with the original packing-density definition.

`ratioMinimizingBody` is chosen from that proved existence theorem.
`ratioMinimizingBoundary` is the explicit gauge-rescaling homeomorphism. Its
restriction to the unit circle is antipodal and injective, covers the entire
frontier, and is Lipschitz. The Lipschitz proof bounds inverse gauge on the
circle using an outer radius, combines this with the Lipschitz gauge, and
estimates the difference of the scaled unit vectors. These are radial boundary
properties, not the still-needed balanced frame or Lipschitz tangent properties.

`all_discs_ratio_bound_of_minimizer_frame` connects the new minimizer to the
existing certificate: a FrameTrace for an area-preserving linear image of that
constructed body would imply the strict bound for all discs' hexagon ratios. Critical-hexagon contact geometry,
the balanced-frame construction/regularity, and the general ratio-to-packing
comparison remain to be formalized. None is introduced as an axiom.

Eleven new modules and 21 named audit entries were added. The prior 114-theorem
report is preserved in `logs/final/verification_before_minimizer_construction.json`.
All 1,180 previous non-root dependency modules retain their audited source,
artifact, and companion hashes (`logs/minimizer_construction_prior_integrity.json`).
Final importing-audit and source-scan results are recorded below after completion.

Final verification passed for all 135 named theorem audits, with only `propext`,
`Classical.choice`, and `Quot.sound`. The import manifest covers 1,192 local
modules. All 1,466 local Lean source files pass the unfinished-proof/custom-axiom/
`native_decide` token scan. The current-source status pass retains all 248 matrix
proofs, 248 Gram expansions, 75 multipliers, four reductions, 248 assembled blocks,
and four complete identities; no component reports are stale. Ratio minimizer,
scalar normalization, radial boundary construction and Lipschitz regularity,
and global ratio comparison flags are true. Balanced frame construction and
unconditional packing density remain false. Evidence:
`logs/final/verification.json`, `logs/final_minimizer_construction_audit.log`,
`logs/minimizer_construction_status.json`, and
`logs/minimizer_construction_source_scan.json`.


## General packing comparison, attained hexagons, and irreducibility

This continuation closes the general hexagon-ratio/original-packing comparison
and proves that the hexagon-area infimum is attained.

For arbitrary Hex, including degeneracies, the middle vertex in lattice
coordinates lies in [0,1/2]^2. This determines the common signs of its fan
triangles. A six-triangle null-overlap assembly gives area at least covolume.
The strip map formed by the first two normals' sum and the third normal is
invertible, proving boundedness and compactness without assuming independent
adjacent sides. Hex is a genuine symmetric convex disc. Applying the already
verified lattice-density theorem to the hexagon itself gives area at most
covolume, hence exact equality. The resulting general comparison
`hexagonRatio_le_packingDensity` uses an infimum argument and does not assume
that the infimum is attained or that lattice packings are globally optimal.

Hexagon parameters consist of twelve real normal/vertex coordinates. A fixed
inner diamond bounds the normals, while the area of triangles containing an
inner diameter bounds the vertices. The bounded enclosing family is compact;
nonvanishing determinant follows from closed incidence constraints. A continuous
determinant minimum gives an actual minimum-area enclosing hexagon of every
symmetric convex disc. The constructed minimizing body has a chosen such
hexagon of area and covolume exactly 2*sqrt(3).

Strict area monotonicity under proper inclusion follows from a positive-area
open difference and closure of the convex body's interior. The area-minimal
property then proves irreducibility of the ratio minimizer. The entire critical
hexagon family is compact and nonempty; its contact locus is compact and lies
in the frontier. This does not yet prove that the contact locus covers the
frontier, or that those contacts are edge midpoints.

An explicit linear equivalence sends two independent edge midpoints to the
first two sixth roots of unity. Their algebraic relations normalize all six
midpoints. The chosen area normalization makes its absolute determinant one,
and preserves global ratio minimality. Midpoint membership in the body is not
silently assumed by this initial coordinate normalization.

`all_discs_packing_bound_of_minimizer_frame` now concludes the original
universal density bound from a balanced frame for an area-preserving image of
the constructed minimizing body. The remaining work is the critical midpoint
contact/coverage theorem, the monotone family and C1/Lipschitz-tangent
regularity, and extraction of the normalized six-arc frame. There is no longer
an independent density comparison or hexagon-attainment gap.

Thirteen modules and 22 named theorem audits were added. The prior report is
preserved in `logs/final/verification_before_hexagon_attainment.json`. All 1,191
previous non-root dependency modules retain their source, artifact, and
companion hashes (`logs/hexagon_attainment_prior_integrity.json`). Final audit
and current-source status results are recorded below after completion.

Final importing verification passed for all 157 named theorem audits. The
manifest covers 1,205 local modules; the only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. All 1,479 Lean source files pass the
unfinished-proof/custom-axiom/`native_decide` scan. The independent current-source
status check reports no stale components and retains all 248 matrix proofs,
248 Gram expansions, 75 multipliers, four reductions, 248 assembled blocks,
and four complete identities. General hexagon area, ratio-to-packing comparison,
critical hexagon attainment, contact compactness, irreducibility, initial
normalization, and universal conditional packing reduction are verified.
Balanced frame construction and the unconditional density theorem remain false.
Evidence: `logs/final/verification.json`,
`logs/final_hexagon_attainment_audit.log`,
`logs/hexagon_attainment_status.json`, and
`logs/hexagon_attainment_source_scan.json`.

The remaining construction was checked against the actual `FrameTrajectory`
and `FrameTrace` interfaces and the local Hales--Vajjha source, Chapter 2.
It needs midpoint contact and coverage, a monotone family, and enough tangent
regularity for absolutely continuous frame-state coordinates. Compactness of
the critical contact locus alone does not establish these requirements.
No existence theorem for that frame has been asserted.


## Critical-hexagon midpoint contacts and nondegeneracy

This continuation proves the midpoint-contact step for every critical hexagon
of the constructed minimizer. Convex separation of a missing midpoint gives
a new strip functional that still encloses the body. Explicit intersection
formulas vary the two adjacent vertices while keeping the other strips fixed.
An exact determinant-difference identity retains the quadratic term; its
linear coefficient has a strict sign. Continuity then supplies a smaller
enclosing hexagon, contradicting criticality. Relabeling handles both
orientations and all six sides.

The strict-side hypothesis is discharged, rather than retained in the final
minimizer theorem. Any non-strict represented hexagon is a linear image of
a square, proved directly from its incidence constraints and redundant-strip
identities. A proper symmetric convex subdisc of a square misses a corner;
compactness supplies a positive corner cut, giving an enclosing hexagon with
area strictly below four. Strict convexity and hexagon attainment also give
a comparison body with ratio below one, so the ratio minimizer cannot itself
be a hexagon. Together these facts prove that every critical hexagon of the
minimizer has six genuine sides.

`criticalHexagon_of_minimizer_midpoint_frontier` concludes all six actual
frontier contacts without a strictness or midpoint-membership hypothesis.
The initial normalized body therefore has the six regular roots on its
frontier and contains their convex hull. Full boundary coverage, uniqueness/
monotonicity, tangent regularity, and construction of the balanced frame
remain unproved. No assumption has been added to hide these remaining steps.

Eight Lean modules and sixteen named audit targets were added. All 1,204
previous non-root dependency source/artifact/companion hashes are unchanged
(`logs/midpoint_contacts_prior_integrity.json`). The prior report is preserved
in `logs/final/verification_before_midpoint_contacts.json`. Final importing
audit and current-source status results are recorded below after completion.

Final combined verification passed for all 173 named theorem audits, with only
`propext`, `Classical.choice`, and `Quot.sound`. The current manifest covers
1,213 local modules. All 1,487 Lean source files pass the unfinished-proof,
custom-axiom, and `native_decide` scan. The independent current-source status
check reports no stale components and preserves all 248 matrix proofs, 248
Gram expansions, 75 multipliers, four reductions, 248 assembled blocks, and
four complete identities. The new midpoint-contact, nondegeneracy, and
normalized boundary-root flags are true. Balanced frame construction and the
unconditional density theorem remain false.

Evidence: `logs/final/verification.json`,
`logs/final_midpoint_contacts_audit.log`,
`logs/midpoint_contacts_status.json`, and
`logs/midpoint_contacts_source_scan.json`. A tool-connection reset interrupted
the first combined-audit attempt; the restarted combined audit completed
successfully and produced the current report.


## Unique supporting lines and continuous normals at critical midpoints

This continuation proves that every critical midpoint of the constructed
minimizer has a unique supporting line. The exact side-variation formula is
specialized to variations fixing the midpoint. Its linear term vanishes and
the area change is exactly t^2 * (zeta a)^2 * det(slideA,slideB) divided by
the two positive intersection denominators. Strict side inequalities force
the slide determinant negative. A distinct supporting form therefore permits
a smaller enclosing hexagon, contradicting criticality.

Admissible small variations are factored into a reusable construction. Cyclic
relabeling covers all six sides, and orientation reversal handles either
determinant sign. A separate normalization theorem proves that every nonzero
supporting functional of a body containing zero in its interior has positive
support level. Consequently the uniqueness theorem describes actual supporting
lines, rather than only a convention for unit/normalized normal coordinates.
The result transfers to the six roots on the initially normalized body.

The critical midpoint set is a continuous image of the compact critical-hexagon
parameter family, and all six midpoints of every critical hexagon belong to it.
It is a compact subset of the frontier. Support uniqueness makes the normal
coefficients constant on the fibers of the midpoint projection. The continuous
surjection from a compact parameter space to the Hausdorff midpoint set is a
quotient map, so its descended support-normal function is continuous.

These results do not assert that critical midpoints cover the full frontier,
that the family is monotone, that the boundary is C1, or that the normals are
Lipschitz. Those remain geometric steps before constructing the balanced frame.

A further argument proves uniqueness of the geometric critical hexagon at a
shared midpoint. Matching orientations makes its signed area agree. The next
midpoint then differs only by a multiple of the common midpoint vector.
Positivity of each neighboring support form on the first midpoint rules out
displacement in either direction. The midpoint configurations agree, and the
unique support forms identify all three strips. Equality is of actual regions,
not labeled Hex records. This supplies a unique critical region at every point
of the critical midpoint set, without presupposing full boundary coverage.

Eight modules and twenty named audit targets were added. All 1,212 prior non-root
dependency modules retain their source, artifact, and companion hashes, as
recorded in `logs/midpoint_tangents_prior_integrity.json`. The prior audit is
preserved in `logs/final/verification_before_midpoint_tangents.json`.
Final importing-audit and current-source status results follow after completion.

The final assembly theorem first passed Lean, but its build wrapper ran out of
disk while saving metadata. The old cache expanded shared import graphs into
large repeated JSON trees (45 GB in the records directory). Build records now
use a lossless shared-node JSON encoding; loading reconstructs the same values,
and the source, artifact, compiler, and dependency comparisons are unchanged.
Legacy plain and gzip records remain readable. Five regression tests cover
round trips, shared references, changed hashes, literal reference keys,
malformed/cyclic references, and all three loading formats.

Two old records were losslessly gzip-compressed, verifying SHA-256 against the
original bytes before replacing the uncompressed copy. This recovered about
15.7 GiB without removing any proof, source, compiled artifact, or record data.
Evidence: `logs/cache_lossless_compression.json`,
`logs/shared_record_encoding_tests.log`, and the preserved first attempt in
`logs/minimizer_critical_hexagon_uniqueness_disk_full.log`.

Next geometric target: distinguish the existing `criticalContactSet` (points
on edges of critical hexagons) from `criticalMidpointSet` (the side midpoints).
HV Lemma 2.2.5 first uses shaving and minimality to obtain edge-contact coverage
and global uniqueness of supporting lines. Monotonicity and full midpoint
coverage occur later. Neither coverage statement follows merely from the
compactness proved here. The new pointwise critical-region uniqueness can be
used without assuming either coverage statement.

Final verification passed: all 193 named theorem audits use only `propext`,
`Classical.choice`, and `Quot.sound`. The current manifest covers 1,221 local
modules, and all 1,495 Lean source files pass the unfinished-proof/custom-axiom/
`native_decide` scan. Comparing the completed manifest to the prior report
confirms all 1,212 prior non-root modules still have identical source, artifact,
and companion hashes (`logs/midpoint_tangents_final_integrity.json`).

The independent current-source status check reports no stale components,
preserves all 248 matrix proofs, 248 Gram expansions, 75 multipliers, four
reductions, 248 assembled blocks, and four identities, and sets the three new
midpoint-support/normal-continuity/critical-hexagon-uniqueness flags to true.
Balanced frame construction and the full unconditional density theorem remain
false. Final evidence: `logs/final/verification.json`,
`logs/final_midpoint_tangents_audit.log`, `logs/midpoint_tangents_status.json`,
and `logs/midpoint_tangents_source_scan.json`.

## Supporting-face contacts and closed convex hull reconstruction

This continuation formalizes a precise part of the trimming/compactness
argument, without presupposing full boundary coverage. `supportCut K psi c`
is the symmetric slab cut of an actual convex disc. The levels
`shaveScale n = 1 - (1 / (n + 1)) / 2` lie in `[1/2,1)` and tend to one.
Each cut contains the corresponding homothetic copy of the original body.
Convexity, compactness, symmetry, and nonempty interior of the cuts are proved.

For an irreducible disc, each proper cut has a strictly smaller enclosing
hexagon. That hexagon excludes some point of the original body. The pairs of
hexagon parameters and excluded points lie in a fixed compact set. Passing to
a subsequence proves that the limiting hexagon encloses the original body,
has exactly critical area, and touches the limiting point. The excluded points
approach one of the two supporting faces of the cut; symmetry puts the contact
on the requested face. This proves `support_face_meets_criticalContactSet` and
its specialization to the constructed minimizer. If a supporting face is a
singleton, its exposed point is therefore a critical contact.

The supporting-face theorem also implies that every nonzero linear functional
achieves its maximum at a critical contact. Hahn–Banach separation then proves
that the closed convex hull of the critical contact locus equals the entire
minimizing body. This is a reconstruction theorem for the body, not an equality
between its boundary and the contact locus.

Four modules and ten named audit targets were added:
`SymmetricSupportCuts`, `CriticalHexagonLimitTools`,
`MinimizerSupportFaceContact`, and `MinimizerContactHull`.
The prior 193-theorem report is preserved in
`logs/final/verification_before_support_face_contact.json`; initial integrity
checks preserved all 1,220 previous non-root source/artifact/companion records
(`logs/support_face_contact_prior_integrity.json`).

Still unproved: contact at every point of a flat supporting face, full boundary
coverage by critical midpoints, global tangent uniqueness/regularity,
monotonicity, and the balanced frame. The existing midpoint uniqueness and
normal-continuity results remain unchanged. Final importing-audit and
current-source status evidence follows after completion.

The first checkpoint passed all 203 named audits, covering 1,225 local modules.
All 1,499 then-current Lean sources passed the unfinished-proof/custom-axiom
scan, and the status report had no stale components. This checkpoint is saved
in `logs/final/verification_support_face_checkpoint.json`.

### Stronger midpoint-on-face argument

Further work in the same continuation strengthens the face-contact result.
A linear form supporting a slab cut at a point strictly inside the slab also
supports the whole original convex body. Otherwise a sufficiently short
segment from the uncut support point toward a violating point would still lie
in the cut and violate its support inequality.

Apply this at all six side midpoints of the smaller minimum enclosing hexagons.
Their limiting critical hexagon is strict, so the cut hexagons are eventually
strict too. The previously proved midpoint-contact theorem therefore applies
to the cuts. If all limiting midpoints avoided the two shaved faces, all six
nearby midpoints would lie strictly inside the cut slab. Locality would then
make the smaller hexagon enclose the original body, contradicting its critical
area. Thus every supporting face contains a critical midpoint.

This yields two further consequences under final verification. A support form
of a face equals the unique support form at its critical midpoint, so every
point of the face lies on an edge of that critical hexagon. Also, the average
of two support forms at any boundary point supports the body; at the critical
midpoint of its face, both original forms attain level one. Midpoint support
uniqueness forces them to agree. This proves global supporting-line uniqueness
without first constructing a boundary parametrization.

The three stronger modules have now built successfully: `SupportCutLocality`,
`MinimizerSupportFaceMidpoint`, and `MinimizerBoundarySupport`. The limiting
midpoint argument, full boundary edge-contact coverage, and global uniqueness
of normalized support forms use only the standard Lean axioms. In particular,
`criticalContactSet_eq_frontier_minimizer` and
`minimizer_frontier_unique_normalized_support` close the boundary-contact and
no-corners conclusions of HV Lemma 2.2.5. The earlier note that flat-face contact
coverage was still open describes the intermediate checkpoint, not the final
mathematical result of this continuation.

The final combined audit now contains 211 targets. The remaining gap is full
critical-midpoint coverage and the monotone family, followed by parametrized
C1/Lipschitz-tangent regularity and balanced-frame construction. Equality of
the contact locus with the boundary is not being substituted for equality of
the midpoint set with the boundary.

Next route from the local reference: HV Lemma 2.2.6 proves monotonicity using
the six normalized triangles, the midpoint relation `s2 = s1 - s0`, and the
positive fixed determinant. Lemma 2.2.7 then excludes gaps in the midpoint
locus using this monotonicity and the now-proved edge-contact/no-corners
results. Critical-region uniqueness at a shared midpoint was already proved
independently in the previous continuation.

Final combined verification passed for all 211 named theorem audits, using only
`propext`, `Classical.choice`, and `Quot.sound`. The current manifest covers
1,228 local modules. All 1,502 Lean source files pass the unfinished-proof,
custom-axiom, and `native_decide` scan. The independent current-source status
reports no stale components and retains all 248 matrix proofs, 248 Gram
expansions, 75 multipliers, four reductions, 248 assembled blocks, and four
complete identities. All six new face/contact/hull/midpoint/coverage/uniqueness
flags are true. Balanced-frame construction and the full density theorem
remain false.

The final manifest preserves all 1,220 prior non-root module records from the
193-theorem baseline and all 1,224 non-root records from the intermediate
203-theorem checkpoint, including source, artifact, and companion hashes.
Evidence: `logs/final/verification.json`, `logs/final_boundary_support_audit.log`,
`logs/boundary_support_status.json`, `logs/boundary_support_source_scan.json`,
and `logs/boundary_support_final_integrity.json`.


## Continuation: continuous critical family and C1 radial boundary

Preserved the prior 211-target report as
`logs/final/verification_before_midpoint_dynamics.json` before changing the
root imports or audit target list. The prior Lean dependencies are unchanged.

`CriticalMidpointDynamics` restricts the compact critical parameter family to
positive orientation. Matching the first midpoint then fixes all six midpoint
coordinates by the previously proved determinant/support argument. The
first-midpoint projection onto the actual critical midpoint locus is
surjective and is a compact quotient map. Its next-midpoint coordinates
therefore descend to a continuous map on that locus.

`CriticalMidpointCycle` identifies this map with cyclic side relabeling. Its
second iterate is `N(p)-p`, its third is `-p`, and its sixth is `p`. Its inverse
is five successive applications, yielding a homeomorphism. The determinant
`det(p,N(p))` equals `sqrt(3)/2`; no point is fixed, and all six midpoint
coordinates vary continuously. The domain is still the actual critical
midpoint set. Neither full-boundary coverage nor cyclic order preservation
is smuggled into these definitions.

`MinimizerBoundaryNormalContinuity` uses the compact space of critical
parameters paired with positive first-side contacts. It projects onto the
entire minimizer boundary. Global supporting-form uniqueness makes the normal
coefficients constant on fibers, proving global continuity, including at
flat-face endpoints. Rotating the support normal gives a continuous nonzero
supporting tangent direction `t(p)` with `det(p,t(p))=1`. It agrees with the
previous normal on critical midpoints.

`MinimizerGaugeDifferentiability` then supplies the missing derivative step.
For a continuous field of supporting affine forms, the first-order remainder
is squeezed between zero and the change in form applied to the displacement.
This proves a general derivative lemma. Applied to the normalized support form
at `x/gauge(K,x)`, it proves that the gauge is C1 away from the origin. Thus
`x/gauge(K,x)` is C1 there and agrees on the unit circle with the already
constructed radial boundary homeomorphism. The explicit chain-rule velocity
has determinant `gauge(K,x)^(-2)*det(x,v)` with the projected position, so
transverse velocities do not vanish. This is radial regularity, not a
Lipschitz tangent estimate or the required balanced family.

The combined audit has been extended from 211 to 242 named targets. Seven new
current-source status flags distinguish midpoint continuity/cycles, global
normal/tangent continuity, C1 gauge/radial regularity, and nonvanishing
transverse derivatives. The root imports, provenance, and README have been
updated. Final importing audit and preservation checks follow below.

Remaining geometric work: prove critical-midpoint monotonicity and full
boundary coverage, prove Lipschitz tangent estimates and the required
regularity of the balanced critical family, then construct FrameTrajectory
and FrameTrace. The local HV Lemmas 2.2.6–2.2.7 remain the source route for
monotonicity/coverage. The new C1 radial boundary removes the earlier need to
establish basic differentiability from scratch; it does not imply the stronger
Lipschitz derivative requirement.

The next regularity source is HV Section 2.4.1: Lemma 2.4.2 transfers C1
regularity from one boundary arc to the other critical midpoint arcs using
fixed determinant and nonzero transverse tangent evaluation. With the new
C1 gauge, an implicit-function proof of that transfer is a possible local
route once midpoint coverage is available. Lemma 2.4.3 is substantially
stronger: its Lipschitz estimate uses interior hyperbola barriers, uniform
curvature control, and arclength parametrization. Those barriers and estimates
are not consequences asserted by the C1 proof in this continuation.

Final combined verification passed all 242 named audits (31 added), with only
`propext`, `Classical.choice`, and `Quot.sound`. The manifest now covers 1,232
local modules. All 1,506 production Lean sources pass the comment-aware scan
for unfinished proofs, custom axioms, and native_decide, and the scan's source
hash is current. All 1,227 prior non-root manifest records are preserved
exactly, including source, artifact, and companion hashes. No audited result
was removed.

The independent current-source status has no stale components. It retains all
248 matrix proofs, 248 Gram expansions, 75 multipliers, four reductions, 248
assembled blocks, and four complete identities. All seven new continuity,
cycle, C1, and transverse-regularity flags are true. Balanced-frame construction
and the unconditional density theorem remain false.

Evidence: `logs/final/verification.json`,
`logs/final_midpoint_dynamics_audit.log`,
`logs/midpoint_dynamics_status.json`,
`logs/midpoint_dynamics_source_scan.json`, and
`logs/midpoint_dynamics_final_integrity.json`.

## 2026-10-28: faster checked iteration and implicit-function prerequisites

The dominant build overhead was dependency bookkeeping, not Lean elaboration.
A fresh checked build of unchanged `CriticalMidpointCycle.lean` took 273.686 s,
including 248.170 s of dependency validation and 24.576 s in Lean. After the
changes below, the identical invocation took 34.721 s, including 12.022 s of
validation and 22.671 s in Lean: 7.88 times faster overall and 20.64 times
faster validation. This is a single before/after observation, not a statistical
benchmark or a forecast of mathematical completion time. Both invocations
compiled afresh because the same 154 legacy imports lack provenance. That
conservative cache-admission rule has not been relaxed.

The first change replaces repeated recursive dictionary equality with exact
memoized comparisons of shared dependency graphs. Every key, ordered list
entry, and scalar is still checked; the memo lives only for one comparison.
Source, artifact, companion, toolchain, option, pre-admission, and post-build
checks remain. Deep shared-graph, mutation, mismatch, and randomized comparison
tests were added. An older profiling test was corrected to read the logical
record through the decoder before deliberately writing its legacy form.

The second change addresses the larger legacy issue. There were about 31 GB
of metadata, including individual records approaching 4 GB. A streaming,
one-off converter compacted 111 old records from 29,687,986,237 bytes to
93,031,639 bytes. Before each atomic replacement, it independently expanded
the serialized compact representation and compared every JSON parse event
against the original, including key/list order and scalar types. This freed
29,594,954,598 bytes without changing proof sources or artifacts. The converter
uses a project-local ijson installation; the ordinary wrapper has no new
third-party dependency. The initial equality-only benchmark was interrupted
and is not used as evidence. Conversion itself took about 480 s, amortized
across future builds. All 27 cache/conversion regression tests pass.

The new `CriticalMidpointTransversality.lean` has five checked results. It
identifies the gauge gradient at a critical midpoint with its side normal,
proves positivity of the next midpoint's normal on the starting midpoint,
proves the constraint linearization has nonzero determinant, identifies it
as the actual Frechet derivative in the second point, and constructs its
invertible continuous-linear-map witness. The constraints are
`(gauge(K,q),det(p,q))`. These supply the nondegeneracy prerequisite for using
mathlib's C1 implicit-function theorem near an existing critical pair.
The checked build took 34.626 s, with 21.633 s in Lean.

The shortened route is now explicit:

1. Establish full critical-midpoint coverage and order using the existing
   compact locus, successor, and support-face results. Edge-contact coverage
   alone is not midpoint coverage.
2. Apply the C1 implicit-function theorem to the two constraints, and identify
   its local branch with the already continuous successor. Reuse the existing
   regular radial boundary and six-cycle identities. The local implicit branch
   itself has not yet been assembled in this continuation.
3. Prove the stronger tangent estimates needed by the state coordinates.
   C1 position curves alone do not imply those estimates. Target the actual
   absolute-continuity requirements in `FrameTrajectory`; avoid reproducing
   stronger published machinery unless needed to prove them.
4. Assemble the normalized six-arc frame and trace, then invoke the existing
   universal minimizer-to-packing reduction.

Evidence: `logs/workflow_speed_benchmark.json`, `logs/cache_compaction.jsonl`,
`logs/transversality_build.log`, and `logs/workflow_speed_source_scan.json`.
The comment/string-aware source scan covers all 1,507 production Lean sources
and finds no unfinished proof, custom axiom, or native_decide token. Combined
root verification and preservation checks are recorded below when complete.

Final combined verification passed all 247 named results, with only `propext`,
`Classical.choice`, and `Quot.sound`. The root build and importing audit took
33.125 s and 29.575 s (62.699 s total), compared with 355.931 s and 370.521 s
(726.452 s total) in the prior 242-target audit. This broader historical
comparison is about 11.6 times faster; the controlled same-module comparison
above remains the cleaner timing measurement.

All 1,231 prior non-root manifest records are preserved exactly, including
source, artifact, and companion hashes. The current manifest contains 1,233
local modules. No theorem was removed and no unexpected axiom appeared.
Current-source status has no stale component reports and retains all 248
matrix checks, 248 Gram expansions, 75 multipliers, 248 assembled blocks,
four polynomial reductions, and four assembled identities. The new
transversality flag is true. Balanced-frame construction and the unconditional
density theorem remain false.

Final evidence: `logs/final/verification.json`,
`logs/final_workflow_speed_audit.log`, `logs/workflow_speed_status.json`,
and `logs/workflow_speed_final_integrity.json`.

## 2026-10-28: local C1 successor, orientation, and regular curve transport

The implicit-function route is now implemented, rather than only proposed.
`CriticalMidpointImplicit` proves C1 regularity of the two-variable constraint
map and identifies its invertible partial derivative in the second point.
Mathlib's implicit-function theorem supplies an ambient local extension around
each critical midpoint pair. It fixes the correct base value and satisfies the
fixed gauge/determinant equations. Local uniqueness, combined with the already
proved continuity of the actual successor, shows agreement with that successor
on nearby points of the actual midpoint locus. No boundary-coverage assumption
is used. Any C1 curve in the locus transports the six configuration coordinates
along C1 curves by the existing balance identities.

`CriticalMidpointOrientation` computes the strict derivative of this extension.
For `q=N(p)`, put `a=D gauge(K,p)[q]` and `b=D gauge(K,q)[p]`. Strictness of the
critical hexagon gives `0<a<1` and `0<b<1`. If `T(p)` is the normalized oriented
supporting tangent, with `det(p,T(p))=1`, the derivative sends it to
`(a/b) T(q)`. This multiplier is continuous on the compact midpoint locus,
hence uniformly bounded above and away from zero. The determinant identity

    det(p,q) det(T(p),T(q)) = 1-a*b

then gives strictly positive determinants for adjacent tangents and adjacent
velocities. This is useful for the later determinant-normalizing time change.
The results concern the local extension and first-order transport. They do not
assert a Lipschitz modulus for variation of the boundary tangent itself.

`CriticalMidpointRegularCurves` links this derivative to actual trajectories.
It proves the radial/tangent decomposition

    v = D gauge(K,p)[v] p + det(p,v) T(p).

A differentiable curve in the midpoint locus has gauge constantly one, so its
velocity annihilates the gauge derivative. Nonzero tangent velocities remain
nonzero under the successor. Consequently the successor of a supplied regular
curve is regular, without an extra tangency assumption. This does not supply
the still-missing full boundary curve in the locus.

The three checked builds passed, with compiler times 21.30 s, 34.74 s, and
27.18 s (total invocation times 33.29 s, 48.37 s, and 41.49 s). The combined
audit was extended by 28 named results to 275. Six current-source flags track
local C1 extension, C1 curve transport, positive tangent transport, uniform
scale bounds, adjacent-velocity nondegeneracy, and regular-curve transport.

Remaining work is full critical-midpoint coverage and global cyclic order,
the stronger tangent regularity needed by the state coordinates, and assembly
of the normalized `FrameTrajectory` and `FrameTrace`. Once a regular boundary
curve in the locus is established, the local regularity transfer no longer
needs a separate arclength-based construction.

Evidence: `logs/implicit_build.log`, `logs/orientation_build.log`,
`logs/regular_curves_build.log`, and `logs/implicit_successor_source_scan.json`.

Final verification passed all 275 named audits (28 added), with only `propext`,
`Classical.choice`, and `Quot.sound`. All 1,232 prior non-root manifest records
are preserved exactly, including source, artifact, and companion hashes. No
audited result was removed. The current manifest covers 1,236 local modules;
the comment/string-aware scan of all 1,510 production Lean sources finds no
unfinished proof, custom axiom, or native_decide token.

All six new current-source status flags are true, with no stale component
reports. The complete numerical certificate remains checked. Balanced-frame
construction and the unconditional packing-density theorem remain false.
The root build and final importing audit took 69.35 s and 39.62 s respectively.
Final evidence: `logs/final/verification.json`,
`logs/final_implicit_successor_audit.log`, `logs/implicit_successor_status.json`,
and `logs/implicit_successor_final_integrity.json`.

## 2026-10-28: supporting-face endpoints and flat-gap reduction

The next coverage step uses a shorter convex-geometric route than a general
compact-convex-hull theorem. `CriticalMidpointSupportFace` first upgrades
support-function maximization from critical edge contacts to actual side
midpoints. For a normalized support form `psi` and a second linear form `chi`,
choose critical midpoints maximizing `psi + chi/(n+1)`. Compactness gives a
subsequence converging to a critical midpoint in the original support face.
The maximizing inequality also proves that this limit maximizes `chi` on
that face. Applying the result to both signs of a tangent coordinate gives
both endpoints of every face. The existing radial/tangent decomposition
identifies the face exactly with their closed segment.

`CriticalMidpointBoundaryGaps` proves the resulting geometric conclusions:

- Every boundary point lies on a flat boundary segment with critical
  endpoints; singleton segments are allowed.
- Every extreme point of the actual minimizer is a critical midpoint.
- The ordinary convex hull of the critical-midpoint locus equals the
  minimizing body, without needing a closure operation. Boundary segments
  supply boundary membership in the hull, antipodal midpoints supply zero,
  and the gauge radial projection supplies all remaining body points.
- Any missing midpoint lies strictly inside a nontrivial flat segment.
  Compactness of the midpoint sets on either side gives nearest critical
  endpoints, and the open segment between them contains no critical midpoint.

These statements use the constructed minimizer and existing critical locus;
there is no supplied boundary-coverage or strict-convexity assumption. The
last statement constructs a genuine flat gap conditional on a missing point;
it does not prove the gap impossible. Global cyclic order and propagation of
gaps between adjacent midpoint arcs still remain. Lipschitz tangent regularity
and assembly of the balanced frame also remain, so the unconditional packing
theorem must stay unverified.

Two missing standard mathlib modules, `Analysis.Convex.Extreme` and
`Analysis.Convex.Strict.Extreme`, were built from unchanged pinned sources
into the project-local overlay. The shared pinned source cache was untouched.
The two new production modules add 12 named audit targets and four status
flags for support-face endpoints, extreme-point coverage, midpoint-hull
reconstruction, and flat-gap reduction.

Final verification passed all 287 named audits (12 added), with only `propext`,
`Classical.choice`, and `Quot.sound`. All 1,235 prior non-root manifest entries
are identical, including their source, artifact, and companion hashes. The
current manifest covers 1,238 local modules. A comment/string-aware scan of
all 1,512 production Lean sources found no unfinished proof, custom axiom,
or `native_decide` token. Both added library sources match the pinned mathlib
originals byte-for-byte.

The checked support-face and gap module builds took 57.16 s and 44.89 s;
the combined root build and importing audit took 35.42 s and 40.67 s. All
four new status flags are true with no stale component reports. The complete
numerical certificate remains intact: 248 matrix proofs, 248 Gram expansions,
75 multipliers, four reductions, 248 assembled blocks, and four identities.
The balanced-frame and unconditional-density flags remain false.

Evidence: `logs/midpoint_faces_build.log`, `logs/midpoint_gaps_build.log`,
`logs/final_midpoint_faces_audit.log`, `logs/final/verification.json`,
`logs/midpoint_faces_status.json`, `logs/midpoint_faces_source_scan.json`,
and `logs/midpoint_faces_final_integrity.json`.

## 2026-10-28: global order and full midpoint coverage

The remaining flat-gap argument is now formalized. Five production modules
close the global order and midpoint-coverage obligations and expose the
successor on the whole boundary.

`CriticalMidpointSectors` works in the basis of consecutive reference
midpoints. Positive combinations of the two points lie in the associated
triangle: normalized support inequalities bound each coordinate by one,
and the gauge triangle inequality bounds their sum below by one. For strictly
positive coordinates all three inequalities are strict. Support uniqueness
and the already proved strict adjacent support evaluation exclude the base
edge; no strict-convexity assumption on the whole body is made. Six sign cases
cover the entire boundary by the six reference triangles. A separate 36-case
linear-inequality proof uses the balance relation and positive determinant to
place the next two points in the next two triangles.

`CriticalMidpointOrder` uses the fixed critical determinant to exclude the
endpoint cases, then applies the strict cone theorem. This proves that all
successive midpoint pairs advance through the corresponding open sectors.
Splitting an open semicircle into three sectors and its two internal endpoint
rays upgrades this to global positive-determinant preservation. Sixfold
periodicity proves the converse:

    0 < det(N(p),N(q)) iff 0 < det(p,q).

This is global order on the actual midpoint locus, rather than only a local
derivative orientation statement.

`CriticalMidpointArcGaps` turns flat gaps into empty angular intervals and
transports empty intervals under the successor, using its surjectivity and
the global determinant equivalence. Conversely, an empty angular interval
has a common support form at its endpoints: in their linear basis every
critical midpoint satisfies the sum-of-coordinates bound, and the proved
convex-hull reconstruction extends that bound to the whole body. Support
uniqueness identifies the endpoint gauge gradients.

`CriticalMidpointCoverage` compares three successive endpoint pairs. Their
three oriented normals agree, so the corresponding supporting-line
intersections, and hence the first side midpoints, agree. This contradicts
a nontrivial empty interval. Distinct endpoints of a flat gap have nonzero
determinant; reversing them if necessary reduces to the positive case.
The previously constructed flat-gap theorem therefore proves

    criticalMidpointSet = frontier ratioMinimizingBody.

The existence and geometric uniqueness of a critical hexagon now hold at
**every** boundary point. These complete the monotonicity and coverage
conclusions of HV Lemmas 2.2.6 and 2.2.7. The proof reuses the earlier strict
support and compact-hull results rather than duplicating the paper's longer
base-edge exclusion argument.

`MinimizerBoundarySuccessor` transports the homeomorphism to the entire
boundary, retaining the balance identity, sixfold periodicity, fixed
positive determinant, and global order comparison. Existing C1 and regular
curve transport now apply to arbitrary boundary curves. The sixfold identity
uses a locally increased elaboration recursion limit for the nested
homeomorphism coercions; no trust or proof-checking option is changed.

The remaining work is stronger tangent regularity sufficient for absolutely
continuous state coordinates, determinant-normalizing parametrization, and
assembly of the normalized `FrameTrajectory`/`FrameTrace`. The unconditional
packing theorem is still not claimed. Current documentation and status
reporting have been updated to remove coverage and global order from the
remaining obligations.

The first combined audit passed all 320 named targets (33 added). A source
scan of all 1,517 production Lean files found no unfinished proof, custom
axiom, or native_decide token. Source and artifact hashes for all 1,237 prior
non-root modules are unchanged. One stale scope sentence in the provenance
notes was then corrected; the audit is rerun to refresh its provenance hash.

The five checked component builds took 41.76 s, 52.59 s, 61.44 s, 73.01 s,
and 44.94 s, respectively. The next published regularity target is HV Lemma
2.4.3: the interior tangent hyperbolas give a uniform curvature bound and
hence Lipschitz tangents. The existing implicit derivative formula can then
transfer this regularity between the six arcs. This geometric bound is not
yet formalized; continuity and bounded tangent-speed transport alone do not
replace it.

Final verification passed all **320** named audits, with 33 added and none
removed. Only `propext`, `Classical.choice`, and `Quot.sound` occur. All 1,237
prior non-root manifest records, including companion hashes, are identical.
The current manifest covers 1,243 local modules; the source scan covers 1,517
production Lean files. The recorded published-provenance hash is current.

All four new current-source status flags are true: global midpoint order,
full boundary coverage, the whole-boundary successor homeomorphism, and
regular-curve transport on the whole boundary. There are no stale reports.
All numerical certificate counts remain intact: 248 matrix proofs, 248 Gram
expansions, 75 multipliers, four reductions, 248 assembled blocks, and four
identities. The balanced-frame and unconditional-density flags remain false.
The final root build and importing audit took 60.62 s and 57.93 s.

Evidence: `logs/final_midpoint_order_coverage_audit.log`,
`logs/final/verification.json`, `logs/midpoint_order_coverage_status.json`,
`logs/midpoint_order_coverage_source_scan.json`,
`logs/midpoint_order_coverage_final_integrity.json`, and
`logs/midpoint_order_coverage_new_modules.json`.


## Exact support coercivity and pointwise tangent bounds

Continued the remaining tangent-regularity work via the already checked
exact side-variation formula. This avoids introducing hyperbolic envelopes
and rolling-circle geometry at this stage.

`HexagonSupportCoercivity` proves a polarization identity for the full
quadratic term, including changes that do not fix the old midpoint. If
`D = det(a,b)`, `S = det(slideA,slideB)`, and `zeta = psi-phi1`, minimality
and a valid replacement support give

    (-S) * (zeta(a)^2 + zeta(b)^2)
      <= 2*D*(1-psi((a+b)/2))*(2+zeta(slideA)+zeta(slideB)).

For a strict positively oriented hexagon `D > 0` and `S < 0`. Bounding the
slide evaluations gives a square bound with coefficient `8*D/(-S)`.

`HexagonSupportRegularity` proves admissibility of all sufficiently small
normal perturbations, not merely perturbations in one fixed direction.
Endpoint evaluations control the entire continuous linear form because
the two side endpoints form a basis. This converts the square bound to
operator norm. If the new support touches at q and the old midpoint is m,
its deficit is at most `(psi-phi1)(q-m)`, hence at most the product of the
normal-change norm and displacement norm. Cancelling gives the anchored
linear displacement bound.

`MinimizerPointwiseRegularity` uses the proved full boundary coverage and
continuity of the gauge gradient to apply this bound at every boundary
point. A fixed linear rotation of the gradient gives the chosen oriented
tangent, so its displacement satisfies an analogous estimate.

Scope: for each p there is a constant C_p and neighborhood on which the
difference from the tangent at p is bounded by C_p times displacement.
This does not assert a common constant over the compact boundary, a
two-point local Lipschitz bound, or absolute continuity. The next step is
to make the quantitative constants uniform over the compact critical
family (or otherwise prove the needed absolute continuity), then perform
determinant normalization and assemble the balanced frame. The full
unconditional density theorem remains unfinished.

All three component modules have passed checked builds. Thirteen named
targets are added to the combined audit; final audit results follow below.

Final combined verification passed all **333** named targets (13 added,
none removed), using only `propext`, `Classical.choice`, and `Quot.sound`.
All 1,242 prior non-root source/artifact/companion records are identical.
The manifest now contains 1,246 local modules; all 1,520 production Lean
sources pass the unfinished-proof/custom-axiom/trust-bypass token scan.
The published-provenance hash is current and there are no stale reports.

The three checked component builds took 35.55 s, 42.85 s, and 33.07 s.
All numerical counts remain intact: 248 matrices, 248 Gram expansions,
75 multipliers, four reductions, 248 assembled blocks, and four identities.
The new coercivity and pointwise gradient/tangent flags are true. Uniform
tangent Lipschitz regularity, balanced-frame construction, and the full
unconditional packing theorem remain false.

Evidence: `logs/final/verification.json`,
`logs/final_tangent_coercivity_audit.log`,
`logs/tangent_coercivity_source_scan.json`,
`logs/tangent_coercivity_status.json`, and
`logs/tangent_coercivity_final_integrity.json`.


## Uniform tangent bounds and the explicit angular boundary

The uniform tangent bound is now proved, upgrading the previous anchored
pointwise estimates to a global Lipschitz theorem on the entire boundary.

`CriticalFamilyRegularity` treats the whole compact positive critical family.
The hexagon vertices, normalized normals, and slide vectors vary continuously.
The coefficient `8*det(a,b)/(-det(slideA,slideB))` is positive and bounded above.
For normal conditioning, consider the sum of squared endpoint evaluations on
the product of this family with the unit sphere of continuous linear forms.
It is continuous and strictly positive because the endpoints form a basis.
Its reciprocal is bounded on that compact product, giving a uniform operator
norm square bound for all hexagons and all linear forms.

`CriticalFamilyUniformVariation` proves validity jointly as the normal
perturbation and hexagon vary, using strict inequalities and positive area.
The compact tube-neighborhood theorem supplies one perturbation neighborhood
valid for every member. Combining both uniform coefficients with the exact
coercivity inequality gives a uniform support-contact displacement bound.
A continuous choice of hexagon representatives is not needed.

`MinimizerUniformRegularity` applies this to the gradient difference for two
nearby boundary points. A product neighborhood yields genuine two-point
local Lipschitz regularity, and the compact local-to-global theorem supplies
a global bound. The fixed linear rotation carries this bound to the oriented
tangent normalized by `det(p,T(p))=1`. Every Lipschitz boundary parametrization
therefore has absolutely continuous gradient and tangent fields on bounded
intervals. The normalized tangent is not described as a unit tangent.

`MinimizerAngularBoundary` explicitly composes the unit-circle angular map
with radial projection. It is C1 and Lipschitz, has positive position/velocity
determinant, and has nonzero velocity everywhere. Tangency and the planar
vector decomposition give the exact velocity formula

    gamma'(t) = gauge(K,(cos(t),sin(t)))^(-2) * T(gamma(t)).

The scalar factor is C1; the tangent field is absolutely continuous. Their
product proves absolute continuity of the actual velocity on every bounded
interval. The neighboring critical-successor curve is constructed as a
regular C1 curve. Its velocity absolute continuity is not yet asserted.

The remaining tasks are propagation of velocity absolute continuity to the
balanced successor curves, selecting a fundamental arc, determinant-normalizing
time, and assembling FrameTrajectory/FrameTrace with endpoint, weak-star, ODE,
and disjoint-arc obligations. The frame and unconditional packing theorem
remain unfinished. Forty-one new named targets are added to the combined audit.

Final combined verification passed all **374** named targets (41 added,
none removed), using only `propext`, `Classical.choice`, and `Quot.sound`.
All 1,245 prior non-root source/artifact/companion records are unchanged.
The manifest contains 1,250 local modules; all 1,524 production Lean sources
pass the unfinished-proof/custom-axiom/trust-bypass token scan. The source
scan and published-provenance hash are current, with no stale reports.

The four checked component builds took 45.04 s, 20.66 s, 25.40 s, and 28.50 s.
The numerical certificate still has 248 matrices, 248 Gram expansions,
75 multipliers, four reductions, 248 assembled blocks, and four identities.
The uniform gradient/tangent Lipschitz and explicit angular regularity/velocity
AC flags are true. The balanced-frame and unconditional-packing flags remain
false. No inference from C1 regularity alone to velocity AC is used.

Evidence: `logs/final/verification.json`, `logs/final_uniform_tangent_audit.log`,
`logs/uniform_tangent_new_targets.json`, `logs/uniform_tangent_source_scan.json`,
`logs/uniform_tangent_status.json`, and `logs/uniform_tangent_final_integrity.json`.


## Successor velocities, the global determinant clock, and the actual state

Constructed the six balanced angular curves and verified AC of their actual
velocities. The successor derivative is expressed through the position/velocity
determinant, positive tangent scale, and successor tangent. New reusable AC
lemmas cover Lipschitz composition, positive reciprocals, planar determinants,
and evaluation of varying linear forms on varying vectors. They avoid any
inference from C1 position regularity alone to AC of velocity.

The adjacent velocity determinant is positive. Its scaled square root defines
the determinant-normalizing speed. Periodicity supplies a uniform positive
lower bound; the integral clock is a strictly increasing surjective C1 map.
Its order-isomorphism inverse is C1 with reciprocal-speed derivative. Actual
reparametrized boundary curves now have adjacent velocity determinant sqrt(3)/2.
A general AC transport lemma for a Lipschitz order isomorphism preserves the
disjoint interval condition and proves AC of all six normalized velocities.

The state matrix uses columns gamma_0 and (2*gamma_1-gamma_0)/sqrt(3).
Position and velocity determinants are one; the mixed determinant is zero.
These identities define its three velocity coordinates and verify the full
determinant constraints and group ODE. Every certificate coordinate is AC.
The six state root images and state tangent images agree with the constructed
boundary curves and their actual velocities.

A first state-assembly build hit the 180-second compiler limit. The final
proof removes broad nonlinear search, rewrites the mixed-determinant identity
before arithmetic, and uses explicit linear combinations for the ODE. This
changes the proof implementation, not the statement or hypotheses.

Still outstanding: weak-star signs for this state, selection of a fundamental
arc, initial frame normalization, rotated terminal state, coverage, and
disjoint arc interiors. Complete FrameTrajectory/FrameTrace construction and
the unconditional packing theorem remain unproved. Final build and audit
results are recorded below when verification completes.


Final verification passed **447 named targets**, including
**73 new targets**, with none removed. All depend only on
`propext`, `Classical.choice`, and `Quot.sound`. All **1249**
prior non-root source/artifact/companion records are unchanged. The manifest
contains **1257** local modules; all **1531**
production Lean sources pass the unfinished-proof, custom-axiom, and
trust-bypass token scan. Provenance hashes are current and there are no stale
reports. The numerical certificate remains 248 matrices, 248 Gram expansions,
75 multipliers, four reductions, 248 assembled blocks, and four identities.

Checked component compiler times (seconds): {"boundary_ac": 22.21, "successor_velocity": 36.21, "determinant_clock": 15.55, "clock_inverse": 34.59, "balanced_regularity": 41.25, "balanced_state": 9.96, "frame_boundary": 14.63}.
The state proof that previously timed out now checks in 9.96 s.
All five new milestone flags are true; full-frame and unconditional-density
flags remain false.

Evidence: `logs/final/verification.json`,
`logs/final_normalized_boundary_audit.log`,
`logs/normalized_boundary_new_targets.json`,
`logs/normalized_boundary_source_scan.json`,
`logs/normalized_boundary_status.json`, and
`logs/normalized_boundary_final_integrity.json`.
The integrity check is reproducible with
`python3 logs/verify_normalized_boundary_integrity.py` after refreshing status.

Implementation note for continuation: these curves live on
`ratioMinimizingBody`, not `initiallyNormalizedMinimizer`. Do not assume the
initial state matrix is the identity or that the fundamental angular endpoint
is pi/3. Its initial matrix has determinant one, so an orientation-preserving
linear normalization by its inverse is available. The first fundamental arc
should end at the actual successor of the initial point. Its endpoint velocity
matching should follow from positive tangent transport and the fixed adjacent
velocity determinant; the terminal state must still be proved, not assumed.


## 2026-10-28 — Complete fundamental arc, normalized frame, and unconditional density bound

The requested improved universal lower-bound formalization is complete. The final
`Certificate.Packing.reinhardt_density_lower_bound` proves, for every set K in
the Euclidean plane satisfying the original `IsSymmetricConvexDisc K`,

```lean
(8950112 : ℝ) / 10000000 < packingDensity K
```

There are no additional minimizer, boundary, regularity, trajectory, or published
geometric assumptions. The corresponding universal hexagon-ratio bound is also
proved. This result is the improved lower bound, not the Reinhardt conjecture
identifying the optimal shape; certificate discovery/optimization is outside
this proof.

The continuation added ten modules and 80 audited declarations:

- `MinimizerStateStars`: tangent transport and strict neighboring support imply
  the three positive star coordinates for the actually constructed state.
- `MinimizerFundamentalAngle`: construct the unique initial-arc endpoint at the
  actual successor, with angle in (0, pi), and a positive determinant-clock duration.
- `MinimizerEndpointVelocities`: positivity, tangency, and the fixed adjacent
  velocity determinant give uniqueness of normalized tangent speed and exact
  endpoint matching for both neighboring curves.
- `InitialFrameNormalization`: left multiplication by the inverse initial frame
  preserves the state equations and has determinant one; the transformed body
  remains a symmetric convex disc and the initial frame becomes the identity.
- `MinimizerTerminalState`: root positions and root tangent velocities determine
  the rotated terminal state. This constructs `minimizerFrameTrajectory`.
- `MinimizerFundamentalArc`: the initial arc has exactly the required sector
  range and is injective on the closed fundamental interval.
- `CriticalMidpointFundamentalPartition`: the six successor sectors and their
  separating midpoints cover the full boundary, using explicit two-dimensional
  coordinate sign cases and positive-ray uniqueness.
- `CriticalMidpointSectorSeparation`: six explicit linear sign tests establish
  disjoint sector interiors.
- `MinimizerFrameTrace`: all six arcs cover the boundary, have disjoint interiors,
  and are individually injective. Transport through the initial inverse frame
  constructs the complete `FrameTrace`.
- `ReinhardtDensityBound`: instantiate the previously conditional universal
  reduction with these constructions and obtain the original packing-density
  conclusion via the proved concrete lattice-packing comparison.

No equal angular spacing or identity initial frame was assumed. The constructed
strict-star theorem concerns the constructed state; the provenance flag claiming
strict endpoints for every abstract frame remains false and is not needed.

Verification completed successfully: all **527** named targets have only
`propext`, `Classical.choice`, and `Quot.sound` as axioms. The final declaration
itself compiled successfully and its axiom report has exactly those standard
axioms. A fresh root build and combined axiom audit both exited successfully.
All **1256** previous non-root source/artifact/companion manifest records are
unchanged. The manifest now contains **1267** local modules. All **1541**
production sources pass the scan for unfinished proofs, custom axioms, and
`native_decide`. Original input, exact-certificate, packing-definition, and
provenance hashes pass; there are no stale reports. The remaining geometric
input list is empty. All seven new milestone flags, including both unconditional
conclusions and `full_density_theorem_verified`, are true.

The numerical certificate is unchanged: 248 matrices, 248 Gram expansions,
75 multipliers, four reductions, 248 assembled blocks, and four identities.
The workflow compiled every new component and reused checked unchanged imports;
it does not claim a separate clean standalone `lake build` was performed.

Successful component compiler times (seconds): {"state_stars": 48.96, "fundamental_angle": 53.66, "endpoint_velocities": 89.92, "initial_frame": 45.19, "terminal_state": 35.77, "fundamental_arc": 35.26, "critical_partition": 51.31, "sector_separation": 40.78, "frame_trace": 30.34, "final_density": 67.08}.
The combined root build took 73.41 seconds including validation; the combined
axiom-audit stage took 68.53 seconds. Queue, validation, and compiler timings
remain separately recorded in the build logs.

Current evidence: `logs/final/verification.json`,
`logs/final_unconditional_audit.log`, `logs/reinhardt_density_build.log`,
`logs/unconditional_new_targets.json`, `logs/unconditional_component_timings.json`,
`logs/unconditional_source_scan.json`, `logs/unconditional_status.json`, and
`logs/unconditional_final_integrity.json`.
The final integrity comparison uses
`logs/final/verification_before_fundamental_arc.json` as its baseline and is
reproducible with `python3 logs/verify_unconditional_integrity.py` after refreshing
status. README and the published-geometry provenance now describe the completed
result and its exact scope.
