# Independent closed-lemniscate bridge: JSP-000410

This package contains a newly written continuous-gauge component argument and its
application to JSP-000410 / Erdős 511. The two new modules are
`JSP410GaugeCore.lean` and `JSP410IndependentClosed.lean`. It contains neither the
former `JSP410ClosedBridge.lean` nor that bridge's verification record. The two
fixed upstream construction modules are references, not vendored sources.

The final statements are
`JSP410Independent.arbitrarily_many_large_closed_components` and
`JSP410Independent.no_uniform_bound_for_large_closed_components`. The first
constructs arbitrarily many distinct actual components of a closed polynomial
sublevel set with diameter greater than `6/5`. This refutes the original assertion
that every threshold greater than one admits a bound independent of degree.
See [SCOPE-AND-ATTRIBUTION.md](SCOPE-AND-ATTRIBUTION.md) for the precise statement
mapping and contribution boundaries.

The mathematical attribution must retain **Christian Pommerenke (1961)** and
**Linhang Huang's independent rediscovery (2025)**; Huang's
[version-two note](https://arxiv.org/html/2509.11597v2) explicitly records the
earlier solution. The fixed upstream formalization credits **Codex / GPT-5.6 Sol**.
The independent core, typed integration, audit and reproduction work were
prepared by **zifanersuotang with Codex assistance**. This is not a first
formalization claim, a new mathematical solution, official acceptance or an award.

## Current verification state

The sources and audit targets are bound by [recipe.json](recipe.json). The actual
fresh Windows execution in [verification.json](verification.json) completed all
nine stages and its serial wrapper with exit code zero: four source compilations,
24 unique axiom reports, 11 printed definitions and four checker runs, each
selecting exactly its intended module. The only reported axioms are `propext`,
`Classical.choice` and `Quot.sound`.

All nine successful logs and all five logs from the earlier failed attempt are
preserved byte for byte. That earlier attempt compiled the four proof modules
but stopped because the audit used invalid same-line import syntax. No checker
stage from that attempt is counted as completed. The two proof files were not
changed by the audit-format repair, and the successful attempt rebuilt all four
custom modules in another fresh directory.

Only absolute executable/output paths in structured command copies were replaced
with labeled placeholders; no stage log was redacted. Default validation
reparses the published logs and rejects missing axiom reports, incorrect module
selection or mismatched source/evidence hashes. Development runs with cached
upstream objects and mock helper tests are not presented as fresh proof evidence.

## Reproduce

Use Python 3.10+, Git, Lean **4.33.0** and its matching `leanchecker`, with an
already populated Mathlib checkout at
`db584cd6d46c92f209a44c0f1c829460d327499d`.

```sh
python verify.py
python verify.py --plan --mathlib /path/to/mathlib --lean-bin /path/to/lean/bin --output /path/to/new-output
python verify.py --execute --mathlib /path/to/mathlib --lean-bin /path/to/lean/bin --output /path/to/new-output
```

Quote paths containing spaces. Default mode reads local metadata, sources and any
published logs. `--plan` only prints commands. Neither mode starts a subprocess,
downloads a source or creates an output directory. Explicit `--execute` requires
a previously unused directory outside this package, Mathlib and the runtime.

Execution downloads exactly `ErdosProblems.Erdos229` and
`ErdosProblems.Erdos511` from `plby/lean-proofs` at
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. It rejects redirects and non-200
responses, checks the exact response URL, bounded byte count, SHA-256 and Git
blob hash, and preserves source bytes and author notices. These dependencies
remain external and retain their own rights; this package makes no upstream
licensing inference.

Nine sequential verification stages are required:

1. Freshly compile `ErdosProblems.Erdos229`.
2. Freshly compile `ErdosProblems.Erdos511`.
3. Freshly compile `JSP410GaugeCore`.
4. Freshly compile `JSP410IndependentClosed`.
5. Compile `Audit410Independent`, checking 24 unique axiom reports and 11 printed definitions.
6. Replay exactly `ErdosProblems.Erdos229`.
7. Replay exactly `ErdosProblems.Erdos511`.
8. Replay exactly `JSP410GaugeCore`.
9. Replay exactly `JSP410IndependentClosed`.

Each checker must actually print its exact one-module selection. Exit code zero
without that output does not pass. All requested axiom reports must occur once
and use only `propext`, `Classical.choice` and `Quot.sound`. Printed definitions
and raw reports are retained. The compiler and audit use `-j1 -M8192`; every
subprocess, including version/Git probes, receives `LEAN_NUM_THREADS=1`.

The private upstream-name resolver in the new integration module is allowed only
at its separately reviewed exact block hash. It selects from an explicit list,
looks up an existing declaration and constructs a constant term. Every typed
wrapper and its uses remain subject to elaboration and kernel replay. Additional
elaborators or active evaluation commands are rejected by the helper.

No old bridge object, compilation event or verification record is reused. The
helper creates fresh `src/`, `build/` and `logs/`, leaves supplied caches
unchanged, and never runs Lake, installs tools or downloads Mathlib. The first
failed compilation, axiom or checker-selection gate stops the run and retains
the real log and failed result. Source, helper, recipe, runtime and log hashes are
checked again after all stages. Raw logs remain unchanged; any later public JSON
copy must label command-path redaction explicitly and retain original hashes.

The verifier uses Lean's kernel with imported cached Mathlib. This is not an
independent kernel implementation, whole-Mathlib replay, or human referee review.
The recorded verification was serialized locally. This portable helper executes
its stages sequentially.
