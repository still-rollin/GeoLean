# Rocq → Lean translation via Claude Code MCP

A second take on the [translation demo](../TRANSLATION_DEMO.md): instead
of a Python orchestrator driving Gemini between two MCP servers, both
servers are mounted directly into Claude Code and Claude does the
translation in-line. No orchestrator, no separate LLM call, no Lake
subprocess — the agent talks MCP to both provers itself.

## What changed vs. the orchestrator demo

```
                Orchestrator demo                       Claude MCP workflow
                ─────────────────                       ───────────────────

           ┌─────────────────────────┐               ┌─────────────────────────┐
           │     orchestrator/       │               │      Claude Code        │
           │       demo.py           │               │   (lean-translation-    │
           │                         │               │       demo branch)      │
           └─┬────────────┬────────┬─┘               └─┬─────────────────────┬─┘
             │            │        │                   │                     │
       (MCP) │       HTTPS│   (MCP)│             (MCP) │                (MCP)│
             ▼            ▼        ▼                   ▼                     ▼
       ┌──────────┐  ┌────────┐ ┌──────────┐    ┌──────────┐         ┌──────────────┐
       │ rocq-mcp │  │ Gemini │ │ lean-lsp │    │ rocq-mcp │         │ lean-lsp-mcp │
       └──────────┘  │  2.5   │ │  -mcp    │    └──────────┘         └──────────────┘
                     │ Flash  │ └──────────┘
                     └────────┘
```

Same three components on both sides; the orchestrator is replaced by
Claude Code itself, and the LLM hop is collapsed into the agent loop.

## MCP wiring

[.mcp.json](../.mcp.json) registers both servers so Claude Code spawns
them on session start:

```json
{
  "mcpServers": {
    "rocq-mcp": {
      "command": "/Users/ayaansiddiqui/GeoCoq/.venv/bin/rocq-mcp",
      "args": [],
      "env": {}
    },
    "lean-lsp-mcp": { ... }
  }
}
```

**Path gotcha:** `rocq-mcp` ships only as a venv entrypoint
(`.venv/bin/rocq-mcp`) and is not on the global `PATH`. The initial
config used the bare name `"rocq-mcp"`, which only works when Claude
Code is launched from an activated venv. The absolute path above works
regardless of how Claude Code is invoked.

Once registered, Claude Code exposes the prover tools under the
`mcp__rocq-mcp__*` and `mcp__lean-lsp-mcp__*` namespaces.

### Tools used in the workflow

| Tool | Role |
|---|---|
| `mcp__rocq-mcp__rocq_start` | Open a `.v` file at a named theorem; returns the parsed goal. |
| `mcp__lean-lsp-mcp__lean_run_code` | Compile a self-contained Lean snippet; returns diagnostics. |
| `mcp__lean-lsp-mcp__lean_diagnostic_messages` | Report errors/warnings for an on-disk Lean file. |

The full menu of MCP tools is broader (proof stepping, hover info, goal
inspection, search), but for the basic extract → translate → verify
loop these three are sufficient.

## The workflow

For each theorem:

1. **Extract** — `rocq_start(file=..., theorem=...)` returns the goal
   string (e.g. `forall n : nat, n + 0 = n`).
2. **Translate** — Claude writes Lean 4 directly.
3. **Verify** — `lean_run_code(code=...)` for a quick in-memory check, or
   `lean_diagnostic_messages` after writing to
   [Scratch.lean](../lean/geocoq_translate/GeocoqTranslate/Scratch.lean).
4. **Repair** — if diagnostics are non-empty, Claude reads the error,
   rewrites, retries. No 3-attempt cap; the loop is just the agent
   loop.

## Demo run

Same five theorems as the orchestrator demo
([theories/Axioms/rocq_demo.v](../theories/Axioms/rocq_demo.v)),
translated and verified end-to-end through MCP. Final consolidated
output in
[lean/geocoq_translate/GeocoqTranslate/Scratch.lean](../lean/geocoq_translate/GeocoqTranslate/Scratch.lean):

| Theorem | Rocq goal | Lean strategy |
|---|---|---|
| `add_0_r` | `∀ n, n + 0 = n` | `rfl` (definitional on `Nat`) |
| `add_comm` | `∀ n m, n + m = m + n` | `induction n` with `Nat.succ_add` / `Nat.add_succ` rewrites |
| `length_app` | `∀ A l l', length (l ++ l') = length l + length l'` | `induction l` with `simp` |
| `de_morgan` | `∀ P Q, ¬(P ∨ Q) ↔ ¬P ∧ ¬Q` | `constructor` + case split on `Or` |
| `exists_not_all` | `∀ P, (∃ n, P n) → ¬ ∀ n, ¬ P n` | destructure existential, apply universal |

One mid-run repair: the first `add_0_r` attempt used `simp [Nat.add_succ, ih]`,
which Lean flagged as a looping simp set. Diagnostics surfaced the
warning ("Possibly looping simp theorem: `Nat.add_succ`"), and the
retry used `rfl` directly.

## Tradeoffs vs. the orchestrator

| | Orchestrator (Gemini)                              | Claude Code MCP                                 |
|---|----------------------------------------------------|-------------------------------------------------|
| Reproducibility | High — scripted, deterministic command            | Low — agent loop, no transcript artifact by default |
| Throughput | Batch-friendly; runs unattended                  | Interactive; one human-in-the-loop session     |
| Cost | Per-token Gemini calls                          | Whatever the Claude Code session costs         |
| Repair budget | Hard-coded `MAX_ATTEMPTS = 3`                    | Open-ended; agent decides when to give up      |
| Best for | Sweeping a corpus, regression runs              | Exploration, hard theorems, tactic discovery   |

The orchestrator path is still the right tool for "translate all of
[file].v unattended". The MCP-direct path is the right tool for
"translate this one tricky theorem and let me poke at it."
