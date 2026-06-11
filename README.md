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

**Tarski_dev chapters**:

| Chapter | State |
|---|---|
| Ch02_cong | Statements + 21 lemmas tagged `@[aesop safe (forward)]` |
| Ch03_bet | **Fully proved** (29 lemmas, no `sorry`) |
| Ch04_col | 14 of 18 proved (includes `l4_13`); `Col_cases`, `Col_perm`, `NCol_perm`, `not_col_distincts` remain |
| Ch04_cong_bet | Statement-only; `l4_6` tagged for aesop |
| Ch05_bet_le … Ch10_line_reflexivity | Statement-only (Phase 0) |

**Euclid Book I**:

- **Proposition 1** — *"On a given finite straight line, to construct an equilateral triangle"* — **fully verified**
- **Proposition 2** — *"To place at a given point a straight line equal to a given straight line"* — **fully verified**

**Supporting `Elements/OriginalProofs` lemmas** (15 verified):

```
lemma_3_5b               lemma_betweennotequal     lemma_doublereverse
lemma_3_6a               lemma_congruenceflip      lemma_extensionunique
lemma_3_6b               lemma_congruencesymmetric lemma_inequalitysymmetric
lemma_3_7a               lemma_congruencetransitive lemma_localextension
lemma_3_7b               lemma_differenceofparts   lemma_NCdistinct
                                                   lemma_NCdistinct
                                                   lemma_partnotequalwhole
```

## Build

Requires [Lean 4](https://leanprover-community.github.io/get_started.html)
(toolchain pinned in [`lean-toolchain`](lean-toolchain)) and Lake.

```bash
lake build
```

Last run: build clean, 0 errors. The only `sorry` declarations sit in
statement-only Phase 0 chapters (Ch04_cong_bet, Ch05–Ch10) and a handful
of section-pinned permutation utilities — none in the transitive closure
of `proposition_01` or `proposition_02`.

## Layout

```
GeocoqTranslate.lean                ← library root, imports every module
GeocoqTranslate/
├── Basic.lean
├── Scratch.lean                    ← throwaway demo translations
├── Tarski/
│   ├── Axioms.lean                 ← tarski_axioms.v
│   └── Definitions.lean            ← Definitions.v (Cong_3, Col, Per, Perp,
│                                     Reflect, ReflectL, Midpoint, …)
├── Euclidean/
│   └── Axioms.lean                 ← euclidean_axioms.v
├── Hilbert/
│   └── Axioms.lean                 ← hilbert_axioms.v
├── Tarski_dev/
│   ├── Ch02_cong.lean              ← congruence basics
│   ├── Ch03_bet.lean               ← betweenness basics (fully proved)
│   ├── Ch04_col.lean               ← Col / nCol permutations + l4_13
│   ├── Ch04_cong_bet.lean          ← Cong+Bet (l4_2, l4_3, l4_5, l4_6 …)
│   ├── Ch05_bet_le.lean            ← Le/Lt segment comparisons
│   ├── Ch06_out_lines.lean         ← Out lines
│   ├── Ch07_midpoint.lean          ← Midpoint theory
│   ├── Ch08_orthogonality.lean     ← Per, Perp, Perp_at
│   ├── Ch09_plane.lean             ← TS, OS, Coplanar
│   └── Ch10_line_reflexivity.lean  ← Reflect, ReflectL + variants
└── Elements/
    └── OriginalProofs/
        ├── euclidean_defs.lean     ← equilateral
        ├── proposition_01.lean     ← Euclid Book I, Prop 1
        ├── proposition_02.lean     ← Euclid Book I, Prop 2
        └── Lemmas/                 ← 15 supporting lemmas
```

## Tooling

### `tools/coqtoleanbrief.py`

Pre-translation helper. Given a Coq lemma name, emits the lemma source +
the Lean signatures of every dependency (top-level decl or class field)
in one block — usable as a CLI or via MCP. Captures multi-line
signatures and class-scoped fields. See `tools/coqtoleanbrief.py --help`.

### `geolean_oracle/`

**Coq proof replay as an MCP server.** Drives `sertop` to capture
`Show Proof.` output and extracts each lemma application's *resolved
positional arguments* — what Coq's `apply`/`eauto` ended up with after
unification, not what the surface syntax says.

```
$ python3 geolean_oracle/__main__.py \
    theories/Elements/OriginalProofs/lemma_3_7a.v lemma_3_7a
=== RESOLVED CALLS ===
lemma_betweennotequal A B C H
lemma_betweennotequal B C D H0
lemma_localextension A C D H1 H2
lemma_congruencesymmetric C C E D H6
lemma_3_6a A B C E H H5
lemma_extensionunique B C D E H0 H8 H7
```

Two MCP tools:

| Tool | Use when |
|---|---|
| `get_resolved_calls(coq_file, lemma_name)` | One-shot lookup during translation |
| `get_resolved_calls_for_file(coq_file)` | Batch-extract for a whole chapter |

See [geolean_oracle/README.md](geolean_oracle/README.md) for architecture,
setup, and MCP registration instructions.

## Design notes and methodology

Three companion documents in [docs/](docs/):

- [**translation_design.md**](docs/translation_design.md) — cross-cutting
  design choices (`Point` as a `Type` parameter, `extends` for class
  hierarchy, snake_case names, two-class split for derived predicates)
  and a per-file walkthrough.
- [**lean_lsp_errors.md**](docs/lean_lsp_errors.md) — every point during
  translation where `lean-lsp-mcp` returned `success: false`, with the
  error message, root cause, and fix.
- [**claude_mcp_workflow.md**](docs/claude_mcp_workflow.md) — the
  Claude Code + `rocq-mcp` + `lean-lsp-mcp` + `geolean-oracle` workflow.
- [**aesop_pilot.md**](docs/aesop_pilot.md) — honest experiment results
  on aesop kill-rate (≪ initial optimistic estimate, see doc for the
  numbers).
- [**phase0_skeleton.md**](docs/phase0_skeleton.md) — chapter-by-chapter
  progress tracker for the statement-only Phase 0 effort.

## Status

This is still a pilot / proof-of-concept rather than a complete port,
but it has expanded since the initial commit:

1. **Two verified Euclid propositions** end-to-end (Prop 1 + Prop 2)
   with zero `sorry` in transitive closure.
2. **Backbone Tarski machinery** through Ch03 fully proved, Ch04+
   statements in place.
3. **Tooling for accelerating translation** — the brief tool eliminates
   signature-lookup round-trips, and the oracle eliminates
   argument-order guessing by replaying Coq's actual unification.

The work demonstrates that:

- Coq → Lean 4 translation of synthetic geometry is technically
  feasible — both axiom-level and proof-level.
- Axiom-level translation is mostly mechanical (~1× expansion).
- Proof-level translation is denser (~3–5× expansion), mainly because
  Coq's hint databases (`Cong`, `eauto using`) silently insert
  permutation lemmas that Lean term-mode requires explicit.
- Pure `aesop` doesn't replicate `eauto with cong3` for non-trivial
  proof shapes (see `aesop_pilot.md` for measurements); a hybrid of
  aesop + targeted manual rewrites is the realistic working pattern.
- The single-class-with-default-fields form of axiom translation looks
  tempting but is wrong (overridable + opaque outside the class); the
  two-class split with namespaced `def`s is the correct Lean
  equivalent of Coq's `Definition` semantics. See lean_lsp_errors.md
  §10/§11/§12 for the full story.

## License

Same as upstream GeoCoq: [LGPL-3.0](LICENSE). This work is a derivative
translation of GeoCoq's Coq sources.

## Credit

Translation of [GeoCoq](https://github.com/GeoCoq/GeoCoq)

Translation work done with assistance from Claude Code
([anthropic.com](https://www.anthropic.com)) using `rocq-mcp`,
`lean-lsp-mcp`, and the in-tree `geolean-oracle` MCP server for live
cross-prover verification.
