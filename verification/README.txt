Reinhardt bound: independent Comparator and Nanoda verification

Completed result (2026-10-30)
  VERIFIED by standard Comparator, including Lean kernel replay, and Nanoda.
  Nanoda checked 137,417 declarations without errors. The complete successful
  run took 11,028.729 seconds (3 h 3 min 49 s); all final integrity checks passed.
  See report.txt for the readable summary and report.json for structured results.
  Full receipts: comparator/recorded/20261030T092754Z/.
  Both saved exports were independently rehashed after completion.

Target
  Certificate.Packing.reinhardt_density_lower_bound
  For every origin-symmetric convex compact planar set with nonempty interior,
  its packing density is strictly greater than 8950112 / 10000000.

The reference in comparator/Challenge.lean imports only Mathlib. Its six packing
definitions match the original benchmark byte-for-byte; see reference-review.json.
The reference's single sorry is a statement placeholder, not an allowed axiom
of the solution. There are no definition holes. The allowed solution axioms are
propext, Quot.sound, and Classical.choice.

What is checked
  comparator/Solution.lean imports the existing final theorem. Custom Lake
  targets freshly compile the two entry files against existing dependencies.
  Standard upstream Comparator v4.33.0 exports the entire selected proof
  dependency closure, compares the reference statement and its definitions,
  checks the axiom policy, runs Nanoda, and replays the solution into a fresh
  Lean kernel environment. Existing project theorems are not trusted as axioms.
  This is proof-object verification, not a clean rebuild of every source file.

Mac setup
  Upstream fake-landrun.sh provides no Linux sandbox isolation.
  Comparator's Main.lean, Comparator.lean, and Comparator modules are unchanged.
  capture_export.py records and forwards the upstream exporter byte stream.
  nanoda_launch.py selects two worker threads and enables result logging; the
  pinned Nanoda binary has a recorded 512 MiB worker-stack resource adjustment.
  Neither adjustment changes proof-checking rules or the permitted axioms.
  Receipts require the export given to Comparator and the stream given to Nanoda
  to have identical SHA-256 and byte counts.

Reproduce on this workstation
  cd <this certificate directory>/verification/comparator
  python3 check.py
  Controls only: python3 check.py --controls-only
  Full proof only: python3 check.py --full-only
  paths.json records the existing toolchain, checker, and Mathlib cache paths.
  The macOS timing utility needs normal system access; an enclosing application
  sandbox can deny its timing syscall and make the wrapper report failure.

Receipts
  comparator/recorded/<UTC timestamp>/ contains provenance.json, results.json,
  status.json, per-stage logs, exact exports, Nanoda configurations and results.
  comparator/latest-run.txt identifies the most recent attempt.
  A completed proof requires status.json to state full_proof_verified=true,
  both checker success markers, zero exit status, matching export hashes, and
  a successful postcheck-integrity.json. A started run or completed controls
  alone does not establish verification of the Reinhardt theorem.

The driver records wall time and maximum resident memory, and stops if free
disk space drops below 8 GiB. Postchecks verify that the recorded project
sources/artifacts, harness files, and checker executables did not change.

Scope
  This checks the improved universal lower bound, not the stronger conjecture
  identifying the smoothed octagon as the optimal Reinhardt body. Correctly
  interpreting the reference definitions remains a separate human obligation.

Progress monitoring
  The pinned Nanoda checker reports its result only after all declarations
  finish; it has no live completion counter or progress signal. Its entire
  input is parsed before checking, so bytes read are not proof-check progress.
  Elapsed time, cumulative CPU time, worker activity, and free disk space can
  be monitored without changing or interrupting verification. CPU activity
  alone does not establish progress through declarations or predict finish time.
  With two workers, normal exit of one while the other still checks implies
  at most one declaration remains unfinished. A panic can also end a worker,
  so this is only a conditional diagnostic, never evidence of acceptance.
  Future logging could count completed declarations and identify each worker's
  current declaration. Declaration counts would still not be a time estimate:
  a few expensive declarations can dominate, and Lean replay follows Nanoda.
