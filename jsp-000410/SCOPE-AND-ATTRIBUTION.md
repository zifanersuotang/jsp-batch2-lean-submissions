# JSP-000410 / Erdős 511: complete closed-set negative resolution

## Original quantifiers and the formal answer

The catalog asks about connected components of the **closed** polynomial
lemniscate `L(p) = {z : Complex | norm (p.eval z) <= 1}` for monic complex
polynomials. The original proposed bound is: for every real diameter threshold
`d > 1`, there exists a finite bound independent of the polynomial degree.
The closed formulation and these quantifiers are stated in
[Huang's introduction, version 2](https://arxiv.org/html/2509.11597v2#S1).

The complete formal negative answer is
[`JSP410Independent.no_uniform_bound_for_large_closed_components`](JSP410IndependentClosed.lean#L168).
It negates exactly the assertion that every threshold above one admits a
uniform bound over all monic polynomials. Its constructive precursor is
[`JSP410Independent.arbitrarily_many_large_closed_components`](JSP410IndependentClosed.lean#L135):

```text
For every natural number N, there is one monic complex polynomial p
and an injective family indexed by Fin N of actual connected components
of L(p), each with ordinary metric diameter strictly greater than 6/5.
```

Taking `N = B + 1` refutes any proposed bound `B` at the single threshold `6/5`.
One counterexample threshold fully disproves the universal assertion over all
`d > 1`. A formalization of the stronger published result for every `d < 4` is
not needed for that negative answer and is not claimed here. Nor is a linear
bound in the degree or an algorithm for arbitrary input polynomials claimed.

The family consists of `connectedComponentIn L(p) c`, not just connected subsets.
`component_mem_componentsIn` identifies these with the original upstream
subtype-component image definition `Erdos511.componentsIn`. All indices use the
same monic polynomial from one approximation existence theorem. The proof
establishes boundedness of each component before applying the real-valued
diameter lower bound. Two core endpoints have distance `5/4`, which gives the
strict `6/5` conclusion. No cardinality convention for infinite sets is used.

The pinned upstream target uses the **open** set with norm strictly below one.
This new bridge proves the closed target explicitly: the approximation margin
excludes norm-at-most-one points from a continuous gauge barrier, confining each
closed component. The open and closed statements are not silently identified.

## Mathematical and formalization credit

Mathematical credit remains with **Christian Pommerenke**, *On metric properties
of complex polynomials*, Michigan Mathematical Journal 8 (1961), 97–115, and
**Linhang Huang** for the independent 2025 rediscovery. Huang explicitly records
Pommerenke's earlier solution in the note added to the
[version-2 introduction](https://arxiv.org/html/2509.11597v2#S1).
This submission does not change the catalog's mathematical status or claim new
mathematics for the submitting account.

The analytic construction, approximation estimates and their dependencies come
from `plby/lean-proofs` at
`8822f7ddef30fadbd92e1c6ab4ed897af356af5e`:

- [Erdos511.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos511.lean), whose header credits Pommerenke and Huang for the mathematics and **Codex / GPT-5.6 Sol** for formalization.
- [Erdos229.lean](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos229.lean), the imported analytic dependency, retaining its own source notices.

The new generic gauge/component core, explicit closed-set assembly, audit and
reproduction helper were prepared by **zifanersuotang with Codex assistance**.
The new proof implementer worked from mathematical contracts, declaration types,
necessary data definitions and public Mathlib APIs, without reading the prior
bridge or upstream theorem proof bodies. A separate source-boundary review found
no distinctive nontrivial copied proof-expression block. This records the actual
implementation process; it is not a universal originality or legal attestation.

The version-pinned private-name adapter only checks that a whitelisted constant
exists and constructs an ordinary typed reference. It does not read its proof
value, introduce an axiom, use an evaluator shortcut or modify kernel rules.
Each imported interface is checked against an explicit type. The independently
proved endpoint facts are not added as assumptions.

The old PR32 bridge is not included in this external package. The new MIT grant
applies only to the new first-party implementation and helper identified in the
repository's licensing table. It does not establish rights over, or grant a
license for, the two unvendored upstream source files. Their fixed repository
notice does not identify them as covered by its reference to some external
Apache-2.0 files. Dependency attribution and license limits remain explicit.

## Verification boundary

The recipe pins Lean 4.33.0, Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`, both upstream source blobs and all new
proof bytes. The public verification record distinguishes actual fresh source
compilation, named axiom audits and the exact modules selected by each checker.
Development compilations using previously built dependency objects are not
presented as fresh replay evidence.

Reproduction uses Lean's kernel with cached Mathlib dependencies. It is not an
independent kernel implementation, a fresh replay of all Mathlib, a Linux
execution, a human referee attestation or official acceptance. Repository
ownership and PR submission do not confer solver credit or award eligibility.
