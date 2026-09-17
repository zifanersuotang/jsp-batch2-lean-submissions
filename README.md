# Reproducible Lean proofs for JSP-000410 and JSP-000422

This public repository holds independently authored bridge modules and their
reproduction evidence for two existing catalog submissions. Upstream analytic
sources remain immutable external references. The awards repository receives
catalog text and references only.

| Problem | Complete formal result | Sources, scope and reproduction |
| --- | --- | --- |
| JSP-000410 / Erdős 511 | Negative resolution of the proposed uniform bound for closed polynomial-lemniscate components, using arbitrarily many components of diameter greater than 6/5 | [Package](jsp-000410/README.md), [scope and attribution](jsp-000410/SCOPE-AND-ATTRIBUTION.md), [existing PR32](https://github.com/TheJustinSunPrize/awards/pull/32) |
| JSP-000422 / Erdős 526 | Full original-domain almost-sure once-coverage criterion in the circumference-one open-arc model, including rearrangement and all endpoints | [Package](jsp-000422/README.md), [scope and attribution](SCOPE-AND-ATTRIBUTION.md), [existing PR81](https://github.com/TheJustinSunPrize/awards/pull/81) |

The new core, bridge, audit and reproduction work was prepared by zifanersuotang
with Codex assistance. Mathematical credit remains with the cited authors;
upstream formalization credit remains with its source notices. Repository
ownership and PR submission do not establish solver credit or award eligibility.
See [LICENSING.md](LICENSING.md) for the exact first-party MIT grant and the
unvendored dependency boundaries.

## Verification evidence

The [new JSP410 record](jsp-000410/verification.json) documents a successful
fresh four-module compilation, audit of 24 declarations and four checker runs
covering all four custom modules. Its nine successful logs and five earlier
failed-attempt logs retain their original bytes. The earlier attempt compiled
all proof sources but stopped at an audit import-syntax error; it is not counted
as a successful replay. The new proof replaces the earlier PR32 bridge and does
not copy that bridge's source or use its verification record.

All 39 JSP422 package files remain byte-for-byte equal to awards fork commit
`295372e187b1ce8b5d492b77244bd49a6439c866`, as recorded in
[migration-manifest.json](migration-manifest.json). Historical and fresh Windows
evidence are retained, including all original logs. That migration does not
claim another Lean run.

## Reproduction

Use Python 3.10+, Git, Lean 4.33.0 and its matching leanchecker, and an already
cached Mathlib checkout at `db584cd6d46c92f209a44c0f1c829460d327499d`.
Each package has its own metadata-only default, plan and explicit execution:

```sh
python jsp-000410/verify.py
python jsp-000422/verify.py
python jsp-000410/verify.py --execute --mathlib /path/to/mathlib --lean-bin /path/to/lean/bin --output /path/to/fresh-output
```

Quote paths with spaces and use a new output directory for each execution.
Default mode validates sources and published evidence without subprocesses or
network requests. Explicit execution downloads only hash-pinned dependencies,
compiles every custom source into fresh outputs and checks actual module
selection. It does not install a toolchain, run Lake or modify supplied caches.
Follow each package README for its exact recipe and evidence boundaries.

These records use Lean's kernel and imported cached Mathlib, not an independent
kernel, full Mathlib replay, Linux execution or human referee attestation.
Mathematical review and any acceptance or eligibility decision remain with the
reviewers.
