# Phase 0 — Statement skeleton + first proof cascade for Tarski_dev

Goal of this phase: produce a typed Lean 4 signature for every theorem
in the buildable part of `Main/Tarski_dev/`, with `sorry` for every
proof body, **then run an aesop-based cascade to close the trivial
fraction without writing each proof by hand.**

Statements first (mechanical, ~1:1), proofs second (via aesop where
possible, hand-translation only for the structural ones).

## Why this comes first

Statements translate ~1:1 from Coq to Lean. Proof tactics don't.
Landing the full skeleton means:

- the dependency tree compiles end-to-end as Lean,
- subsequent proof-translation can be done in any order (no missing-
  identifier errors),
- aesop has a real target to chew on,
- progress is a measurable number ("% of `sorry`s closed").

Order of work was driven by the `dpdgraph` analysis in
[`dpdgraph_out/`](../dpdgraph_out/). Tarski_dev chapters go first
because they sit deepest in the dependency tree — most Element
lemmas transitively need them.

## What's landed so far

### Statement coverage

| Chapter file (`.v` → `.lean`) | Lemmas | New defs |
|---|---:|---|
| `Ch02_cong` (prior work)        | 30 | — |
| `Ch03_bet`                      | 22 | `Col`, `Bet_4`, `BetS` |
| `Ch04_col`                      | 16 | — |
| `Ch04_cong_bet`                 |  6 | `IFSC`, `FSC` |
| `Ch05_bet_le`                   | 66 | `Le`, `Lt`, `Ge`, `Gt` |
| `Ch06_out_lines`                | 53 | `Out` |
| `Ch07_midpoint`                 | 55 | `Midpoint` |
| `Ch08_orthogonality`            | 94 | `Per`, `Perp_at`, `Perp` |
| `Ch09_plane`                    |109 | `TS`, `OS`, `Coplanar`, `TSP`, `OSP`, `Saccheri` |
| **Total typed signatures** | **451** | **20 defs** |

### Proofs filled (post-pilot)

| Source | Lemmas proved | Notes |
|---|---:|---|
| `Ch02_cong` (prior work) | 30 | done end-to-end before Phase 0 |
| Prop 1 dependency chain (prior work) | 11 | in `Elements/OriginalProofs/Lemmas/` |
| `Ch04_col` aesop pilot (this session) | 13 | **81% of file**, see below |
| **Total proved** | **54** | |

So Phase 0 currently stands at **54 proved / 451 typed (12%)**, with a
clear path to 35–45% via the aesop cascade.

`lake build` output: **281 jobs, 0 errors**. (Job count jumped from 30
once `import Aesop` and `import Mathlib.Tactic.Tauto` were added —
Mathlib transitively pulls in many modules. Stable after first build.)

## Counting honestly — three views of progress

There are three different ways to measure "how much of Tarski_dev is
done." All three matter for different conversations:

| Metric | Done | Total | % |
|---|---:|---:|---:|
| Chapter numbers with statements (Ch02 … Ch16) | 8 | 15 | **53%** |
| Source `.v` files in `Tarski_dev/` | 9 | 27 | 33% |
| Built `.vo` files in current dune config | 9 | 17 | 53% |
| **Proved-not-sorry within Phase 0** | **54** | **451** | **12%** |

Why the file counts diverge:

- **Several chapters split across multiple files.** Ch04 has
  `_col` + `_cong_bet`; Ch10 has two `_line_reflexivity` files; Ch13
  has six sub-files; Ch14, Ch15, Ch16 have 2–3 each. 15 chapter
  numbers → 27 source files.
- **Ten files aren't compiled by the current build.** Ch12's second
  half (`_inter_dec`), Ch13's last two sub-files, and all of Ch14, Ch15,
  Ch16 depend on `Algebraic/` (coordinate / field-theory) which the
  local dune config doesn't compile. Their statements reference
  identifiers we don't yet have Lean equivalents for, so they're
  blocked until the algebraic layer is translated.

Use the **53% by chapter number** for status emails. Use the **12%
proved coverage** when asked "is anything actually proved."

## Defs added to [`Tarski/Definitions.lean`](../lean/geocoq_translate/GeocoqTranslate/Tarski/Definitions.lean)

Literal ports of the matching Coq `Definition` in
[`theories/Axioms/Definitions.v`](../theories/Axioms/Definitions.v).
Same body, same argument order.

```lean
def OFSC, IFSC, FSC                                 -- five-segment configurations
def Cong_3                                          -- triangle congruence
def Col                                             -- collinearity
def Bet_4, BetS                                     -- 4-point + strict betweenness
def Le, Lt, Ge, Gt                                  -- segment ordering
def Out                                             -- ray
def Midpoint                                        -- midpoint
def Per, Perp_at, Perp                              -- right angles, perpendicularity
def TS, OS                                          -- two-sides / one-side of a line
def Coplanar, TSP, OSP                              -- coplanarity, 3D two-/one-side
def Saccheri                                        -- Saccheri quadrilateral
```

## Translation conventions used

Set in [`translation_design.md`](translation_design.md); applied
uniformly here:

- One `.lean` file per `.v` chapter, same path under
  `lean/geocoq_translate/GeocoqTranslate/Tarski_dev/`.
- `section` per Coq `Section`, with the section's `Context` clause
  becoming a `variable {Tpoint : Type} [Tarski_neutral_dimensionless …]`.
- Lemma names kept verbatim from Coq (`l5_1`, `between_symmetry`, etc.).
- Implicit `forall` in Coq → explicit parameter list in Lean.
- `\/` → `∨`, `/\` → `∧`, `~` → `¬`, `<>` → `≠`, `<->` → `↔`.
- Subscripts where helpful (`A₁`, `A₂`, `h₁`, `h₂`).
- Every theorem body is `:= sorry` by default, replaced with a real
  proof when the aesop cascade or hand translation closes it.

## The aesop cascade (pilot results)

This is the **headline new finding** from the session. Full write-up in
[`aesop_pilot.md`](aesop_pilot.md). Summary here:

### Setup is trivial

```lean
-- One import line per file that uses it:
import Aesop
import Mathlib.Tactic.Tauto

-- Tag four foundational lemmas:
@[aesop safe]          bet_col           : Bet A B C → Col A B C
@[aesop safe]          between_trivial   : Bet A B B
@[aesop safe]          between_trivial2  : Bet A A B
@[aesop safe forward]  between_symmetry  : Bet A B C → Bet C B A
```

That's the entire ruleset for what we tested. Four attribute lines plus
two imports.

### What the cascade looks like

For lemmas like `Col A B C → Col B C A` (pure permutation):

```lean
theorem col_permutation_1 (A B C : Tpoint) (h : Col A B C) : Col B C A := by
  unfold Col at h ⊢
  tauto
```

For lemmas like `Col A B C → Col C B A` (needs `between_symmetry`):

```lean
theorem col_permutation_3 (A B C : Tpoint) (h : Col A B C) : Col C B A := by
  unfold Col at h ⊢
  rcases h with h | h | h <;> aesop
```

`rcases` splits the disjunction so aesop sees a concrete `Bet _ _ _`
hypothesis; the `safe forward` rule on `between_symmetry` then fires
and produces the reversed `Bet`, which aesop matches against one of
the three disjuncts in the goal.

### Pilot kill rate

On `Ch04_col` (16 lemmas, all `sorry` at start of session):

| Status | Count |
|---:|---|
| **Closed by cascade** | **13** (81%) |
| Still `sorry` — section/class mismatch (Col_cases, Col_perm) | 2 |
| Still `sorry` — deeper structural (l4_13 onwards), not in scope of pilot | 1 (of the in-scope set) + 4 deeper |

### What worked, what didn't

**Worked:**
- `unfold + tauto` closes pure permutation goals (no geometry needed).
- `unfold + rcases + aesop` closes one-symmetry-deep goals.
- Term-mode one-liners are best for contrapositives (`¬ Col … → ¬ Col …`).
- Term-mode `.inl (...)` / `.inr (...)` for trivial-existence goals.

**Didn't work — keep in mind:**
- Aesop doesn't fire `Or.intro_left`/`Or.intro_right` to construct
  disjunctive goals from a matching atomic fact. Hand-write the
  `.inl`/`.inr` wrapper.
- Forward rules need a concrete (non-disjunctive) hypothesis to fire.
  Do `rcases` first.
- **Section/class mismatches block downstream calls.** `col_permutation_*`
  live in section T4_1 (`…_with_decidable_point_equality`). They only
  use `between_symmetry`, which is in the weaker
  `Tarski_neutral_dimensionless`. But because T4_1 pinned the stronger
  instance, calling `col_permutation_*` from a weaker T4_3 section
  (where `Col_cases` lives) fails typeclass synthesis. Two fixes:
  (a) weaken sections that don't really need decidability, or
  (b) make the callers require decidability. Leaving as `sorry` for
  now where call sites are few.

### Extrapolation to the rest of Phase 0

Rough estimate over the remaining 397 typed `sorry`s:

| Category | Approx count | Expected close rate |
|---|---:|---:|
| Pure permutation (X ↔ X after unfold) | ~80 | ~95% |
| One-step symmetry (unfold + rcases + aesop) | ~120 | ~85% |
| Trivial existence / `Or` constructions | ~60 | ~60% (term mode) |
| Multi-step structural (l4_13, l5_5, etc.) | ~180 | ~10% (needs hand) |
| Deeper geometry (l8_24, l9_30, etc.) | ~10 | ~0% (needs hand) |

Weighted: **35–45% of 451 should close** with this cascade. That maps
to roughly **160–200 additional lemmas proved** over the project,
ending at ~50% real proof coverage of Phase 0 with no further tactic
research needed.

## Gotchas hit during translation

**Beeson sections take stability as a hypothesis, not a class.** In
`Ch03_bet`, the two `Beeson_*` sections use `Variable Cong_stability`
(resp. `Bet_stability`) inside the section. In Lean we make these
explicit theorem arguments instead:

```lean
theorem l2_11_b
    (Cong_stability : ∀ A B C D : Tpoint, ¬ ¬ Cong A B C D → Cong A B C D)
    (A B C A' B' C' : Tpoint) … : Cong A C A' C' := sorry
```

Not converting these to a typeclass — they're only used twice each
and the local-hypothesis form is closer to Coq's `Variable` semantics.

**`Le P A` followed by a linebreak `P B` is one application.** Coq
auto-formats some long `Le` calls across lines:
```coq
Lemma l6_13_1 : forall P A B, Out P A B -> Le
 P A P B -> Bet P A B.
```
That's `Le P A P B` — four arguments. Easy to mis-read as `Le P A`
plus a stray `P B`.

**Lean is order-sensitive within a file.** `FSC` was first written
above `Col` and the LSP flagged `unknown identifier Col`. Coq's
`Definition` blocks tolerate this; Lean doesn't. Trivial fix (swap
two blocks) but it will hit any later batch translation.

**Some Coq lemmas are commented out.** `Ch09_plane.v` has a `sym_sym`
lemma wrapped in `(* … *)` that references the undefined identifier
`ReflectP`. My initial `awk` extraction picked it up; manually
skipped in the Lean output and noted in the file's top-doc. Worth
running a `Proof. … Qed.` sanity check on the source before believing
any extracted signature list.

**Aesop ruleset gotchas — captured in [`aesop_pilot.md`](aesop_pilot.md).**
The disjunctive-goal limitation and the section-class mismatch are the
two patterns most likely to bite during a full sweep.

## What's next

Four lanes of work, runnable in parallel:

### Lane A — Finish Tarski_dev statements

The remaining 7 buildable files, in dependency order:

| File | Lemmas | New defs needed |
|---|---:|---|
| Ch10_line_reflexivity   |  41 | `ReflectL`, `Reflect`, `ReflectL_at`, `Reflect_at` |
| Ch10_line_reflexivity_2 |  31 | — |
| Ch11_angles             | 278 | `CongA`, `LeA`, `LtA`, `GeA`, `GtA`, `Acute`, `Obtuse`, `InAngle` |
| Ch12_parallel           | ~150 | `Par`, `Par_strict` |
| Ch13_1                  | ~50 | — |
| Ch13_2_length           | ~80 | `Length`, `Is_length`, `Q_Cong`, `Len`, `EqL` |
| Ch13_3_angles           | ~80 | `Q_CongA`, `Ang`, `EqA` |
| Ch13_4_cos              | ~60 | `Lcos`, `Eq_Lcos`, `Lcos2`, `Eq_Lcos2`, `Lcos3`, `Eq_Lcos3` |

Approximate remaining: **~770 lemma signatures, ~20 defs**.
Ch11 alone is the biggest single file (278 lemmas, 11k lines). It
should be its own session.

After this lane: 100% of buildable Tarski_dev has statement coverage.

### Lane B — Aesop cascade across remaining Phase 0

The pilot validated the approach on `Ch04_col` (81% kill). Next steps:

1. **Sweep `Ch03_bet`** — should hit similar % on `bet_neq*__neq`,
   `not_bet_distincts`, etc. Most direct consumers of the rules already
   tagged.
2. **Sweep `Ch02_cong`** — needs `cong_*_commutativity` tagged
   `@[aesop safe]` and `cong_symmetry` tagged `@[aesop safe forward]`.
   Expected kill rate **>80%** because Cong permutation is even more
   uniform than Col.
3. **Sweep `Ch05_bet_le`, `Ch06_out_lines`, `Ch07_midpoint`** —
   measure kill rate per file. Refine the extrapolation table above
   with real numbers.
4. **Decide the section-class question.** Either weaken sections that
   don't really need decidability (cleaner, diverges from Coq's
   structure), or make a few downstream lemmas require it (smaller
   diff, fewer `sorry`s remain).
5. **Consider `@[simp]` for `Col`, `Out`, `BetS`, `Midpoint`** — if
   marked simp-unfolding, aesop wouldn't need the explicit
   `unfold X at h ⊢` step. Test on one file before doing globally.

Estimated total work: ~1 afternoon per chapter, mostly mechanical.
Yields the projected **35–45% real proof coverage** at the end.

### Lane C — Top-5 Element lemmas by in-degree

From the leaderboard in [`dpdgraph_out/`](../dpdgraph_out/):

1. `lemma_collinearorder`   (1390 uses, 129 dependents)
2. `lemma_collinear4`        (480 uses, 85 dependents)
3. `lemma_ray4`              (297 uses, 68 dependents)
4. `lemma_NCorder`           (243 uses, 56 dependents)
5. `lemma_parallelflip`      (165 uses, 38 dependents)

Each one unlocks dozens of downstream Element propositions when proved
(not just stated). These are smaller, more leaf-like lemmas than the
Tarski_dev ones — aesop may close them with a similar cascade once
`Cong` permutations are tagged.

### Lane D — Push current progress to GeoLean repo

The standalone https://github.com/still-rollin/GeoLean repo is now
~30 files behind the working tree (Ch08, Ch09, the aesop pilot edits,
and the new doc files all unsynced). Recommend a sync after Lane A's
Ch10 lands, or whenever a phase-end milestone is hit.

## Out of scope for Phase 0

These need their own phases:

- **Algebraic layer** (`Algebraic/`, ~3 files). Required before
  Ch12_parallel_inter_dec, Ch13_5, Ch13_6, all of Ch14/Ch15/Ch16
  become translatable.
- **Coinc layer** (`Coinc/`, ~5 files). Independent subsystem.
- **Element proofs**. Statements are mostly already translated as
  part of Prop 1's dependency chain; filling proofs is post-Phase-0
  work organized by in-degree, not chapter order.
- **Variant axiom systems** (Beeson, Gupta, Makarios). Deferred per
  earlier mentor conversation — main port targets Tarski as canonical.
- **LeanHammer / Duper integration.** Reserved for the residual after
  aesop sweeps — those tools have higher setup tax and only pay off
  on the structural lemmas aesop can't handle. See the LeanHammer
  discussion thread for the cascade order (aesop → premise-hinted
  aesop → hammer → hand).
