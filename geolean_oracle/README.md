# geolean_oracle

End-to-end **Coq proof replay** for GeoCoq → Lean translation.

Given a `.v` file and a lemma name, returns the list of lemma/axiom applications used in the proof — **name + positional arguments after Coq's unification** — exactly as `Show Proof.` would print them.

This is the key data we lose when translating to Lean by hand: which lemma was called, in what argument order, with which hypotheses. The translator has to re-derive it from scratch, often through 5–6 round-trips of `lean_diagnostic_messages`. With the oracle, those become one-shot translations.

## Status

| Component | State |
|---|---|
| Coq proof → resolved-calls extraction | **Working end-to-end** |
| `lemma_3_6a`, `lemma_3_7a`, `lemma_3_7b` tests | ✅ pass |
| `proposition_01` (25-call trace) | ✅ extracted |
| SerAPI subprocess wrapper | ✅ done |
| Alias resolution (`let e := lemma_X in e args`) | ✅ done |
| MCP server wrapper | ✅ done (`src/server.py`, registered in `.mcp.json`) |
| Bulk extraction (`extract_resolved_calls_for_file`) | ✅ done |
| Compound-arg pretty-printing | partial (paren groups kept verbatim) |

## Usage

```bash
python3 geolean_oracle/__main__.py \
    theories/Elements/OriginalProofs/lemma_3_7a.v lemma_3_7a
```

Output:
```
=== RESOLVED CALLS ===
lemma_betweennotequal A B C H
lemma_betweennotequal B C D H0
lemma_localextension A C D H1 H2
lemma_congruencesymmetric C C E D H6
lemma_3_6a A B C E H H5
lemma_extensionunique B C D E H0 H8 H7
```

Add `--show-proof-term` to also print the raw `Show Proof.` output. Add `--json` for machine-readable output.

## Prerequisites

- `sertop` from the `play_rocq` opam switch (`coq 8.18.0`).
- GeoCoq's `.vo` files must be compiled with the **same** Coq:
  ```bash
  dune build theories/Elements/OriginalProofs/
  ```
  (Takes ~30s for the whole Elements tree, then incremental.)

## Architecture

```
.v file
  ├─→ extract_lemma_source       (regex on Lemma … Qed)
  ├─→ extract_requires           (lines starting with Require)
  ├─→ _extract_section_header    (Section / Context)
  │
  ▼
SerAPI(sertop subprocess)
  │  Add → Exec each chunk
  │  Capture Feedback messages
  ▼
proof term (textual output of Show Proof.)
  │
  ▼
parse_resolved_calls
  │  walk tokens
  │  track `let alias := lemma_X in` substitutions
  │  collect lemma_*/axiom_*/cn_*/proposition_* applications
  ▼
list[ResolvedCall]   ← what the user receives
```

## Files

| Path | Role |
|---|---|
| `src/serapi.py` | Minimal SerAPI client (subprocess + S-exp response classification) |
| `src/oracle.py` | Lemma source extraction, sertop driver, proof-term parser |
| `__main__.py` | CLI |
| `tests/test_oracle.py` | Smoke tests on 3_6a, 3_7a, 3_7b, proposition_01 |

## Limitations (current)

1. **Compound arguments** (e.g. `(fun H : Bet A B C => ...)`) are kept as a single parenthesized string. Translation still has to read these for proofs that use Coq fun-terms (Classical_Prop.NNPP, explicit lambdas). Most GeoCoq Elements proofs don't hit this.
2. **No MCP wrapper yet.** The Python function is callable today; wrapping with `fastmcp` is straightforward (mirror `tools/coqtoleanbrief.py`).
3. **Bulk-extract mode missing.** `extract_resolved_calls_for_file(coq_file) -> dict[name, ResolvedCall list]` would be a useful next step.
4. **Stale .vo files cause cryptic errors.** "inconsistent assumptions over library Coq.Init.Ltac" means a dependency was compiled by a different Coq version. Fix: `dune clean && dune build theories/Elements/OriginalProofs/`.

## MCP integration

Two tools are exposed in `src/server.py`:

| Tool | Use when |
|---|---|
| `get_resolved_calls(coq_file, lemma_name)` | Translating a single lemma — fast targeted lookup |
| `get_resolved_calls_for_file(coq_file)` | Starting a whole chapter — populates oracle data for every proof in one shot |

The server is registered in the repo's `.mcp.json`:

```json
"geolean-oracle": {
  "command": "python3",
  "args": ["-m", "src.server"],
  "cwd": "/Users/ayaansiddiqui/GeoCoq/geolean_oracle",
  "env": { "GEOCOQ_DIR": "/Users/ayaansiddiqui/GeoCoq" }
}
```

Restart Claude Code to pick up the new server. Then the oracle's tools appear alongside `lean-lsp-mcp` and `rocq-mcp`.

## Combined workflow

Pair this with the brief tool to make Coq → Lean translation one-shot:

```
.v lemma
  │
  ├─→ coqtoleanbrief.py    →  Lean signatures of every dependency
  │
  └─→ geolean-oracle MCP    →  Coq's resolved positional arguments
                                for every lemma call in the proof

         translator (me) writes the .lean file in one pass — no
         iteration on argument-order errors, no signature recall
         from memory.
```
