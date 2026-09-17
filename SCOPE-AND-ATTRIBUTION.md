# Scope and attribution: JSP-000422 / Erdős 526

## Original question and complete formal entry

The [original problem](https://www.erdosproblems.com/526) asks for necessary and
sufficient conditions for random arcs to cover every point of a circle almost
surely. Its hypotheses are nonnegative lengths tending to zero and a divergent
sum. They are the domain hypotheses of
[`JSP422FiniteHead.unrestricted_once_exists_rearrangement`](jsp-000422/LargeArcBridge.lean#L185).
No initial ordering, strict positivity or strict subunit bound is required.

The model is the circumference-one quotient circle `R/Z`. An arc is an **open**
metric ball of radius half its length, with independent uniform centers under
the product of normalized Haar measures. Once coverage means that **every point**
belongs to at least one arc; the universal quantifier is inside the sample event.
It is not an almost-everywhere coverage assertion.

For any lengths `a` satisfying the original hypotheses, the final theorem
constructs a decreasing rearrangement `b` of the positive indexed terms and proves

```text
P(onceCoverageEvent a) = 1
  iff (there exists n with 1 <= a n) or SheppCondition b.
```

`SheppCondition b` is divergence of the Shepp series, defined in the pinned
upstream source. The rearrangement is a genuine bijection onto the positive
indices: repetitions are preserved and only zero-length empty arcs are omitted.
The theorem proves existence of this rearrangement. The variant
[`unrestricted_once_criterion`](jsp-000422/LargeArcBridge.lean#L163) works for every
supplied valid rearrangement.

The argument includes all cases:

- Below length one, the finite-prefix bridge relates the probability-one once
  coverage predicate to the probability-one infinite coverage predicate. It
  does not identify the events or all their probabilities.
- At length one, an open arc misses its antipode; independent tail coverage and
  Fubini supply the endpoint argument.
- Above length one, a single arc covers the whole quotient circle.
- Zero lengths and arbitrary initial order are handled by the upstream
  rearrangement construction and the final assembly.

[Shepp's original abstract](https://link.springer.com/article/10.1007/BF02789327)
states the positive, nonincreasing, strictly subunit version of the criterion.
The open-ball convention is explicit in
[Durand's treatment, page 1](https://arxiv.org/pdf/0806.0880). The original problem
website does not specify open versus closed endpoints. This package states its
open-arc model explicitly and does not claim a separate Lean theorem for closed
balls or reproduce the website's abbreviated unsorted-prefix formula verbatim.

## Contribution boundaries

The mathematical solution is due to **L. A. Shepp**, *Covering the circle with
random arcs*, Israel Journal of Mathematics 11 (1972), 328–345. The existing
catalog's solved status and mathematical solver attribution are not changed by
this Lean submission.

The analytic Shepp theorem, circle model and rearrangement construction are
dependencies from `plby/lean-proofs` at full commit
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`. Their source headers and
[attribution record](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/data/sources.yaml#L3821)
credit **Codex / GPT-5.6 Sol** for that formalization. The four upstream files
remain unvendored; [upstream.json](jsp-000422/upstream.json) records immutable
URLs and hashes. Repository ownership is not a claim to their authorship.

The new finite-prefix probability bridge, strict criterion composition, endpoint
assembly, audit and reproduction helper were prepared by **zifanersuotang with
Codex assistance**. These call upstream declarations. Source comparison found no
substantive copied or adapted upstream proof block in the three new bridges;
short conventional Lean scaffolding is shared. See [LICENSING.md](LICENSING.md)
for the exact scope of the new MIT grant and the limits of the upstream notice.

This is formalization and reproduction work, not a new mathematical solver
claim or an independent human referee attestation. PR submission, repository
ownership and automated checking do not confer award eligibility.

## Verification and migration evidence

The proof bytes and all evidence are preserved from awards fork commit
`295372e187b1ce8b5d492b77244bd49a6439c866`; the 39-file
[migration manifest](migration-manifest.json) supplies each byte count and SHA-256.
Historical attempts, including failed attempts, remain unchanged.

The [fresh Windows record](jsp-000422/e2e-windows-20260917.json) documents seven
custom module compilations, one audit of 17 declarations and four checker
invocations selecting all seven custom modules. All twelve stages and the serial
wrapper exited zero. The reported axioms are only `propext`, `Classical.choice`
and `Quot.sound`. The code contains no admitted proof step in this claimed entry.

This migration did not rerun Lean because it preserves the executed source
bytes. The evidence uses Lean's kernel and imported cached Mathlib; it is not an
independent kernel implementation, full Mathlib replay, Linux execution or
official acceptance. Reproduction instructions and pinned versions are in the
[root README](README.md) and [package README](jsp-000422/README.md).
