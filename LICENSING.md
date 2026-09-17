# Licensing and source boundaries

This external version newly provides the [MIT license](LICENSE-MIT) for the
following first-party contribution files. It does not assert that the earlier
awards commits already supplied a separate MIT license for the Lean bridges.
The exact file bytes are preserved, so the license applies to these versions:

| File | SHA-256 |
| --- | --- |
| `jsp-000422/FiniteHeadBridge.lean` | `fd698364426e7c4b17a9033bee19f2dfdc220775de9549b80acd9bcab533e728` |
| `jsp-000422/StrictOnceCriterion.lean` | `fc2888a6b794acfbcc5256d3945ee40f4b20ed15df62030d16eee0577cdda7ea` |
| `jsp-000422/LargeArcBridge.lean` | `132de51db0f2ee4eea092788f941df3112e48c7d2741a6597c4d9a217d5382b9` |
| `jsp-000422/Audit526Bridge.lean` | `c1fa71fbb801b2fa6ae32bcfe4afcedc46eaf6e07336631d98acf2539fb62d89` |
| `jsp-000422/verify.py` | `84cb46b4579ad5e6fec12697c09e9c065d324f23186d539b537c275a35622bce` |

These files were prepared for this submission by zifanersuotang with Codex
assistance. The three bridge modules were compared with the four pinned upstream
modules for the source boundary: their new arguments use the existing API;
the upstream analytic proofs are imported, not copied into these files. General
Lean/Mathlib notation and short conventional tactic scaffolding do not constitute
a claim to the underlying library or mathematics.

The new root README, scope explanation and provenance manifest are also supplied
under MIT. The previously published package README and evidence records are
retained with their original attribution and provenance. No historical license
claim is changed by copying their bytes.

The external sources referenced by `jsp-000422/upstream.json` are **not vendored**
and are not covered by this license. At the fixed `plby/lean-proofs` revision,
[`src/latest/LICENSE`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/LICENSE)
states that some externally sourced files are Apache-2.0; it does not identify
these four files as covered or grant a blanket repository license. This project
does not infer such a license. Each dependency retains its original notices and
its own rights; the helper retrieves its public hash-pinned version for review.

Mathlib and Lean retain their respective licenses and authorship. Linking or
importing their declarations does not transfer those rights to this repository.
The mathematical solution is due to L. A. Shepp; the upstream source headers
credit Codex / GPT-5.6 Sol for their formalization. Neither is claimed as the
repository owner's original work.
