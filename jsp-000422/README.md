# Once coverage for random circle arcs: JSP-000422

Lean bridge sources and evidence for the verified final statements. Both the original Windows validation and a fresh end-to-end Windows run of the published helper completed all compilation, 17-declaration axiom and four kernel-replay gates. The new run used real pinned-source downloads and no private compiled objects. Publication and independent acceptance are separate; no Linux end-to-end result is claimed.

The existing fixed-source formalization gives a Shepp criterion for every point being covered infinitely often. This bridge addresses the event that every point is covered at least once. These events must not be silently identified.

In the existing unit-circle model, an arc centered at z with length l is the open metric ball of radius l/2. Given nonnegative lengths a tending to zero with divergent sum, the proved unrestricted target supplies a decreasing rearrangement b of the positive terms and states:

```text
P(every point is covered at least once) = 1
  iff (some a_n >= 1) or SheppCondition(b).
```

Here SheppCondition is divergence of the sum of exp(b_0 + ... + b_n)/(n+1)^2. Rearrangement is part of the statement; the condition is not asserted for arbitrary unsorted prefix sums.

The new finite-head argument shows that, when every length is strictly below one, probability-one once coverage is equivalent to probability-one infinite coverage. It proves positive probability of missing a fixed point with an independent finite prefix, then uses product-measure sections to handle a point chosen after fixing the tail. It does not interchange an uncountable point quantifier with an almost-everywhere quantifier.

The endpoint branch is explicit. A length greater than one covers the whole circle in this model. A length-one open arc misses its antipode; after fixing the independent head, an independent nonsummable tail hits that fixed antipode almost surely. This extends the pinned model to the unrestricted lengths in the abbreviated problem page. Shepp's original paper assumes strictly subunit lengths, so the endpoint extension is not attributed verbatim to that paper.

## Sources and contribution

- [Catalog JSP-000422 at the reviewed revision](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0401-0500.md#JSP-000422)
- [Erdős problem 526](https://www.erdosproblems.com/526)
- [Existing formalization, fixed commit](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos526.lean)
- [Shepp, Covering the circle with random arcs (1972)](https://link.springer.com/article/10.1007/BF02789327)

The existing formalization's source headers credit L. A. Shepp for the mathematical result and Codex / GPT-5.6 Sol for formalization. Its circle model, analytic estimates, Shepp criterion and rearrangement theorem are reused unchanged. The new contribution is the finite-prefix probability bridge and explicit open-arc endpoint assembly. No priority, first-proof, recipient, eligibility or award determination is made.

The four upstream source files are represented by immutable URLs and byte hashes in upstream.json; they are not vendored. This package contains only the three new bridge files, audit harness, evidence and reproduction helper. The three bridge files and harness are exact verified bytes, with SHA-256 values checked by the helper.

## Actual validation and fresh reproduction

The [fresh public-helper E2E record](e2e-windows-20260917.json), with its twelve [original-byte logs](e2e-logs/07-audit-Audit526Bridge.log), records an actual Windows run on 17 September 2026. The unchanged published `verify.py` downloaded and hash-checked four pinned upstream sources, copied the three included bridges and audit, freshly compiled all seven custom modules, compiled the audit, and ran all four target checkers. All twelve verification stages and the wrapper exited zero. The 17 raw axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`; actual structured-name checker selection covered all seven custom modules. This run used the supplied Mathlib cache read-only and did not reuse the private v4/v5 objects. The evidence preserves the original result digest, source and log digests, actual stage times, and neutral placeholders in command metadata; all twelve log files are unchanged bytes.

The earlier v4/v5 chain remains available below. Its `verification.json` and fifteen historical logs are unchanged; the fresh record supplements them rather than rewriting their provenance.

`verification.json` and the fifteen published logs retain the actual successful evidence and three historical failed-attempt logs. All published logs are byte-for-byte identical to their original logs; both original and published SHA-256 values are recorded, and redaction lists are empty. Private local paths have been omitted from metadata and replaced by generic placeholders in recorded command vectors.

The successful chain has seven custom source compilations. Six actually ran in attempt v4: the four unchanged upstream modules, `FiniteHeadBridge`, and `StrictOnceCriterion`. Their source, object, event and log hashes were checked before and after reuse in v5. Attempt v5 freshly compiled the repaired `LargeArcBridge`, ran the unified audit, and ran four checkers: six new processes, all exiting zero. Original v4 compilation timestamps are preserved rather than represented as v5 executions.

All 17 requested declarations printed only `propext`, `Classical.choice` and `Quot.sound`. The actual structured Lean `Name` selections were the upstream entry plus Core/Weighted/Shepp (four modules), then each separate bridge root (one module each). Thus all seven custom modules received target kernel replay. The main final theorem is `JSP422FiniteHead.unrestricted_once_exists_rearrangement`; the supplied-rearrangement variant is `JSP422FiniteHead.unrestricted_once_criterion`.

`LEAN_NUM_THREADS=1` was requested for child processes, with `-j1 -M8192` additionally passed to source and audit compilation. This is not a measurement of internal OS thread count. Leanchecker does not implement the compiler's memory/thread flags, so the record does not claim that those flags restricted the checker.

The portable helper requires Python 3.10 or later, Lean **4.33.0**, and an already cached Mathlib checkout at **db584cd6d46c92f209a44c0f1c829460d327499d**. It uses the supplied cache read-only. It never installs a toolchain, runs Lake, or downloads a Mathlib cache.

Default metadata/log checking performs no subprocess or network call:

```sh
python verify.py
```

Display the complete fresh command plan without running or downloading anything:

```sh
python verify.py --plan --mathlib /path/to/mathlib --lean-bin /path/to/lean/bin --output /path/to/new-run
```

Execute from final source bytes in a new isolated output directory:

```sh
python verify.py --execute --mathlib /path/to/mathlib --lean-bin /path/to/lean/bin --output /path/to/new-run
```

The output directory must not already exist and must be outside both this package and the Mathlib checkout. Execution downloads the four fixed upstream files, rejects redirects and requires HTTP 200 at each exact pinned raw URL, verifies SHA-256/Git blob IDs and the full import order, copies the three included bridges and audit unchanged, and freshly compiles all seven custom modules. It then compiles the 17-declaration audit and runs all four target checkers: twelve verification subprocesses, plus separate Lean-version and Git-commit probes. It does not consume private cached objects. The first compiler, axiom or checker-selection failure stops the run and leaves its actual logs and result.json in that isolated directory.

`recipe-checks.json` records 29 passing lightweight checks, including changed source/log rejection, unsafe paths, altered downloads, redirect/non-200/changed-URL rejection, thread settings on version probes, missing/nonstandard axiom reports, structural checker scope, output conflicts, a fully mocked twelve-process sequence, failure-stop behavior and unchanged supplied-cache bytes. These isolate helper behavior. The separate actual Windows elaboration and checker run is linked above; neither record claims a Linux end-to-end result.

These checks use Lean's kernel and an imported Mathlib environment. They are not an independent kernel implementation, a fresh replay of all Mathlib, a human referee attestation or official acceptance.
