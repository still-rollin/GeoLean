# GeoLean

A partial Lean 4 translation of [GeoCoq](https://github.com/GeoCoq/GeoCoq),
the Coq library of synthetic geometry.

## What's translated

**Three axiom systems**, fully ported:

- **Tarski** — `Tarski_neutral_dimensionless` + extensions
  (`_with_decidable_point_equality`, `Tarski_2D`, `Tarski_3D`,
  `Tarski_euclidean`, `Tarski_ruler_and_compass`, `Tarski_continuous`)
- **Euclidean** — `euclidean_neutral_basis` + `euclidean_neutral` +
  `euclidean_neutral_ruler_compass` + `euclidean_euclidean` + `area`
- **Hilbert** — `Hilbert_neutral_basis` + `Hilbert_neutral_dimensionless`
  + `_2D` + `_3D` + `Hilbert_euclidean` + `_ID`

**One Tarski_dev chapter** — `Ch02_cong.v` → all 30 congruence-basics
lemmas (T1_1 through T1_4 sections).

**Euclid Book I, Proposition 1** — *"On a given finite straight line, to
construct an equilateral triangle"* — fully verified end-to-end, no
`sorry` in transitive closure. Eleven supporting lemmas from
`Elements/OriginalProofs/` ported as part of the dependency chain.

## Build

Requires [Lean 4](https://leanprover-community.github.io/get_started.html)
(toolchain pinned in [`lean-toolchain`](lean-toolchain)) and Lake.

```bash
lake build
```

Last run: 22 jobs, 0 errors, 0 `sorry` warnings.

## Layout

```
GeocoqTranslate.lean                ← library root, imports every module
GeocoqTranslate/
├── Basic.lean
├── Scratch.lean                    ← throwaway demo translations
├── Tarski/
│   ├── Axioms.lean                 ← tarski_axioms.v
│   └── Definitions.lean            ← Definitions.v (partial: OFSC, Cong_3)
├── Euclidean/
│   └── Axioms.lean                 ← euclidean_axioms.v
├── Hilbert/
│   └── Axioms.lean                 ← hilbert_axioms.v
├── Tarski_dev/
│   └── Ch02_cong.lean              ← Tarski_dev/Ch02_cong.v (30 lemmas)
└── Elements/
    └── OriginalProofs/
        ├── euclidean_defs.lean     ← partial: equilateral
        ├── proposition_01.lean     ← Euclid Book I, Proposition 1
        └── Lemmas/                 ← 11 supporting lemmas
            ├── lemma_3_6a.lean
            ├── lemma_3_7a.lean
            ├── lemma_3_7b.lean
            ├── lemma_betweennotequal.lean
            ├── lemma_congruenceflip.lean
            ├── lemma_congruencesymmetric.lean
            ├── lemma_congruencetransitive.lean
            ├── lemma_extensionunique.lean
            ├── lemma_inequalitysymmetric.lean
            ├── lemma_localextension.lean
            └── lemma_partnotequalwhole.lean
```

## Design notes and methodology

Three companion documents in [docs/](docs/):

- [**translation_design.md**](docs/translation_design.md) — cross-cutting
  design choices (`Point` as a `Type` parameter, `extends` for class
  hierarchy, snake_case names, two-class split for derived predicates)
  and a per-file walkthrough.
- [**lean_lsp_errors.md**](docs/lean_lsp_errors.md) — every point during
  translation where `lean-lsp-mcp` returned `success: false`, with the
  error message, root cause, and fix. Thirteen distinct failure
  patterns documented.
- [**claude_mcp_workflow.md**](docs/claude_mcp_workflow.md) — the
  Claude Code + `rocq-mcp` + `lean-lsp-mcp` workflow used to drive the
  translation.

## Status

Roughly **0.7% of GeoCoq by line count, ~4% by file count**. This is a
pilot/proof-of-concept, not a complete port. The work demonstrates that:

1. Coq → Lean 4 translation of synthetic geometry is technically
   feasible.
2. Axiom-level translation is mostly mechanical (~1× expansion).
3. Proof-level translation is denser (~3-5× expansion), mainly because
   Coq's hint databases (`Cong`, `eauto using`) silently insert
   permutation lemmas that Lean term-mode requires explicit.
4. The single-class-with-default-fields form of axiom translation looks
   tempting but is wrong (overridable + opaque outside the class); the
   two-class split with namespaced `def`s is the correct Lean
   equivalent of Coq's `Definition` semantics. See lean_lsp_errors.md
   §10/§11/§12 for the full story.

## License

Same as upstream GeoCoq: [LGPL-3.0](LICENSE). This work is a derivative
translation of GeoCoq's Coq sources.

## Credit

Translation of [GeoCoq](https://github.com/GeoCoq/GeoCoq), originally
formalized in Coq by Julien Narboux, Pierre Boutry, Guillaume Cano,
and contributors. Refer to the upstream repository for the Coq sources
this work is based on.

Translation work done with assistance from Claude Code
([anthropic.com](https://www.anthropic.com)) using `rocq-mcp` and
`lean-lsp-mcp` for live cross-prover verification.
