# Reproducible Lean proof for JSP-000422 / Erdős 526

This independent public repository contains the proof and evidence associated
with [existing PR81](https://github.com/TheJustinSunPrize/awards/pull/81). It was
prepared to keep the awards repository limited to catalog references under its
updated contribution format. Its history starts with the selected proof package;
it does not copy the awards repository's history or vendor upstream dependencies.

The final theorem is
[`JSP422FiniteHead.unrestricted_once_exists_rearrangement`](jsp-000422/LargeArcBridge.lean).
For nonnegative arc lengths tending to zero with divergent sum, as required by
the original problem, it supplies a decreasing rearrangement of the positive
terms. Almost-sure once coverage holds exactly when some original length is at
least one or the rearranged Shepp series diverges. The proof handles zeros,
arbitrary initial ordering, the length-one endpoint and larger lengths.

See [SCOPE-AND-ATTRIBUTION.md](SCOPE-AND-ATTRIBUTION.md) for the statement mapping
and source boundaries, and [LICENSING.md](LICENSING.md) for the exact newly licensed
first-party files. Repository ownership and PR submission are not solver credits.
Mathematical acceptance and any eligibility decision remain with the reviewers.

## Pinned source and evidence

All 39 files in the existing package are preserved byte for byte from awards
fork commit `295372e187b1ce8b5d492b77244bd49a6439c866`, recorded in
[migration-manifest.json](migration-manifest.json). Its historical verification
record, all fifteen historical logs, fresh Windows record and twelve fresh logs
remain unchanged. No new Lean execution is claimed solely from this migration.

The actual fresh Windows run compiled all seven custom modules, audited 17 named
declarations and ran four checker invocations covering all seven modules. All
twelve stages and the serial wrapper exited zero; the reports contain only
`propext`, `Classical.choice` and `Quot.sound`. The complete original-byte evidence
is in [the package](jsp-000422/README.md) and
[the fresh record](jsp-000422/e2e-windows-20260917.json).

## Reproduction

Use Python 3.10+, Git, Lean 4.33.0 with its matching `leanchecker`, and an already
populated Mathlib checkout at `db584cd6d46c92f209a44c0f1c829460d327499d`.

```sh
python jsp-000422/verify.py
python jsp-000422/verify.py --plan --mathlib /path/to/mathlib --lean-bin /path/to/lean/bin --output /path/to/fresh-output
python jsp-000422/verify.py --execute --mathlib /path/to/mathlib --lean-bin /path/to/lean/bin --output /path/to/fresh-output
```

Quote paths containing spaces. Default mode validates the local source and
published evidence without network or subprocesses. Explicit execution requires
an unused output path outside the package and Mathlib checkout, downloads four
exact hash-pinned upstream files, compiles all seven modules and the audit, and
runs all four target checkers. It reads supplied caches without modifying them
and does not run Lake or install a toolchain. The first failed gate stops the run.

This is Lean's own kernel operating with imported cached Mathlib, not a separate
kernel implementation, a full Mathlib replay, a Linux run, or a human referee
attestation. The reproducible proof package is publicly available for review;
no official acceptance or award is implied.
