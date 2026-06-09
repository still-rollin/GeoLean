# Aesop + tauto pilot — Ch04_col

Goal of this pilot: see whether the **aesop + tauto + light hand-tactics**
cascade can close GeoCoq's "boring" permutation/triviality lemmas without
hand-writing each proof. Test bed: [`Tarski_dev/Ch04_col.lean`](../lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Ch04_col.lean),
16 lemmas total.

## Setup

- Added `import Aesop` to [`Tarski_dev/Ch03_bet.lean`](../lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Ch03_bet.lean).
- Added `import Aesop` + `import Mathlib.Tactic.Tauto` to `Ch04_col.lean`.
- Tagged 4 foundational lemmas with `@[aesop safe]` (or `safe forward`):
  ```
  @[aesop safe]          bet_col           : Bet A B C → Col A B C
  @[aesop safe]          between_trivial   : Bet A B B
  @[aesop safe forward]  between_symmetry  : Bet A B C → Bet C B A
  @[aesop safe]          between_trivial2  : Bet A A B
  ```

That's the entire ruleset. Three `safe` rules + one `safe forward` rule.

## Results

| Lemma | Status | Tactic that closed it |
|---|---|---|
| col_permutation_1 | ✓ proved | `unfold Col; tauto` |
| col_permutation_2 | ✓ proved | `unfold Col; tauto` |
| col_permutation_3 | ✓ proved | `unfold Col; rcases h with h \| h \| h <;> aesop` |
| col_permutation_4 | ✓ proved | same |
| col_permutation_5 | ✓ proved | same |
| not_col_permutation_1 | ✓ proved | term-mode contrapositive |
| not_col_permutation_2 | ✓ proved | term-mode contrapositive |
| not_col_permutation_3 | ✓ proved | term-mode contrapositive |
| not_col_permutation_4 | ✓ proved | term-mode contrapositive |
| not_col_permutation_5 | ✓ proved | term-mode contrapositive |
| col_trivial_1 | ✓ proved | term-mode (`.inl (between_trivial2 ...)`) |
| col_trivial_2 | ✓ proved | term-mode (`.inl (between_trivial ...)`) |
| col_trivial_3 | ✓ proved | term-mode (`.inr (.inr (between_trivial2 ...))`) |
| Col_cases | still `sorry` | section/class mismatch — see below |
| Col_perm | still `sorry` | section/class mismatch — see below |
| l4_13 — col_cong_3_cong_3_eq | not attempted (deeper) | — |

**13 of 16 lemmas closed.** **81% kill rate** on a file that was 100% `sorry`
this morning. Closer to **86%** if you exclude the four deeper l4_* lemmas
that were never intended for the trivial cascade.

`lake build`: 281 jobs, 0 errors. (Job count jumped from 30 because
`import Aesop` and `import Mathlib.Tactic.Tauto` transitively pull a lot
of Mathlib modules into the build.)

## What worked (and what to remember)

**1. `unfold Col; tauto` closes pure-permutation goals.**
For lemmas that only reorder disjuncts (e.g. `Col A B C → Col B C A`),
the goal after unfolding is a propositional identity. `tauto` solves it
without needing any geometry lemmas at all.

**2. `unfold + rcases + aesop` closes "one-`between_symmetry`-deep" goals.**
For `Col A B C → Col C B A` (where you need to reverse each `Bet`), the
pattern is:
```lean
unfold Col at h ⊢
rcases h with h | h | h <;> aesop
```
The `rcases` splits the disjunction so aesop sees a concrete `Bet`
hypothesis. The `@[aesop safe forward]` rule on `between_symmetry` then
fires and produces the reversed `Bet`, which aesop matches against one
of the three disjuncts in the goal.

**3. The contrapositive pattern is one-liner term mode.**
For `¬ Col A B C → ¬ Col B C A`, manually:
```lean
fun h' => h (col_permutation_2 _ _ _ h')
```
Aesop *could* probably close this too if `col_permutation_*` were
tagged, but the term-mode version is shorter and clearer, so kept it.

## What didn't work (lessons)

**1. Aesop doesn't fire `Or.intro_left`/`Or.intro_right` on goals.**
The Col_cases and col_trivial_* lemmas have disjunctive goals
(`Bet A B C ∨ Bet B C A ∨ Bet C A B`). The relevant fact (e.g.
`between_trivial2 : Bet A A B`) matches one disjunct, but aesop's
`safe` rule machinery doesn't try wrapping the goal in `.inl` or
`.inr` to make the match work. Had to hand-write the `.inl (...)`
or `.inr (.inr (...))` wrapper.

**Workaround:** for goals with a `∨` head, write the term-mode proof
explicitly. It's one line, and you know exactly which disjunct you want.

**2. Forward rules need a concrete hypothesis to fire.**
The `@[aesop safe forward]` on `between_symmetry` only fires *after*
`rcases` splits the disjunction. With the goal still a disjunction
(no `Bet _ _ _` in scope as a hypothesis), nothing matches. The
forward rule waits for matter to act on.

**3. Section-class mismatches block downstream calls.**
`col_permutation_*` live in Coq section T4_1, which uses
`Tarski_neutral_dimensionless_with_decidable_point_equality`. The
proofs *don't actually need* decidability — they only need
`between_symmetry`, which is in the weaker `Tarski_neutral_dimensionless`.
But because the section header pinned the stronger instance, calling
`col_permutation_*` from a weaker section (T4_3, where `Col_cases` lives)
fails typeclass synthesis.

**Two ways to fix:** (a) move `col_permutation_*` to a weaker section
(diverges from Coq's structure); (b) make `Col_cases`/`Col_perm` require
decidability (gives up some generality). Either works. Leaving as
`sorry` for now since the call sites are few.

## Extrapolating

Out of **451 sorries** in Phase 0, how many will close to a similar
cascade?

Rough estimate based on this pilot:

| Category | Approx count | Expected close rate |
|---|---:|---:|
| Pure permutation (`X ↔ X` after unfold) | ~80 | ~95% |
| One-step symmetry (`unfold + rcases + aesop`) | ~120 | ~85% |
| Trivial existence / `Or` constructions | ~60 | ~60% (term mode) |
| Multi-step structural (l4_13, l5_5, etc.) | ~180 | ~10% (needs hand) |
| Deeper geometry (l8_24, l9_30, etc.) | ~10 | ~0% (needs hand) |

Weighted average: roughly **35–45% of the 451 should close** with the
cascade. The 30–50% estimate in [`phase0_skeleton.md`](phase0_skeleton.md)
holds up.

## Next steps for the aesop track

1. **Tag the rest of the basic Ch03_bet lemmas** — `bet_neq*__neq`,
   `not_bet_distincts`, `between_inner_transitivity`, etc. Many of
   these are mechanical and will benefit downstream sweeps.

2. **Apply the same sweep to Ch02_cong** — congruence permutations
   are even more numerous than Col permutations. Mark `cong_symmetry`
   `@[aesop safe forward]` and watch what closes.

3. **Decide on the section-class question.** Either weaken sections
   that don't really need decidability, or accept the residual
   sorries where call sites cross boundaries.

4. **Run the cascade across Ch05_bet_le and Ch06_out_lines.** They
   have similar permutation-heavy starts. Measure kill rate per file
   to refine the estimates above.

5. **For the unfold-friendly defs (Col, Out, Midpoint, BetS, …),
   consider adding `@[simp]` to their definitions** so aesop unfolds
   them automatically without needing explicit `unfold Col at h ⊢`.

## Numbers — Phase 0 state after this pilot

- **451** signature-typed theorems in `Tarski_dev/Ch02–Ch09`
- **13** now proved (this pilot, all in Ch04_col)
- **438** still `sorry`
- **30 → 281** build jobs (Aesop + Tauto pulled in Mathlib modules,
  but stable at 281)
- **0 errors**

So we're at **2.9% proved coverage** of Phase 0 already, from one
afternoon's work on one file. Multiplying out the estimates above:
proving the trivial cascade across all 8 chapters should land somewhere
near **160–200 lemmas closed**, hitting **35–45% proved coverage**
without writing more than a few dozen lines of new tactic per file.

## Update — `Ch03_bet` sweep (same session)

After the Ch04_col pilot, the four foundational `sorry`s on the tagged
lemmas (`bet_col`, `between_trivial`, `between_symmetry`,
`between_trivial2`) were filled with real proofs — otherwise every
aesop-closed lemma downstream was sound only modulo those sorries.
Then the rest of `Ch03_bet` got the same sweep treatment.

### Kill rate on Ch03_bet

| Section | Lemmas | Proved | Notes |
|---|---:|---:|---|
| T2_1 (neutral, basic) | 14 | 14 | foundations + bet_neq family + not_bet_distincts |
| T2_2 (inner/outer transitivity) | 2 | 2 | uses `inner_pasch`, `construction_uniqueness` |
| T2_3 (exchange) | 3 | 3 | derived by symmetry from T2_2 |
| T2_4 (existence) | 6 | 5 | `l3_17` skipped (two-step Pasch chain) |
| Beeson_1 | 2 | 0 | stability-hypothesis lemmas, harder pattern |
| Beeson_2 | 2 | 1 | `BetSEq` closed by `Iff.rfl`; other two skipped |
| **Total** | **29** | **25** | **86% kill rate** |

The 4 skipped are all known structural proofs that need hand
translation. The 25 closed include 7 by aesop/tauto, 12 by direct
term-mode applications of the foundation lemmas, and 6 by short
tactic proofs using `inner_pasch` + `between_identity`.

### Patterns that worked beyond what Ch04_col showed

**1. Pasch + between_identity is a recurring motif.** Almost every
proof in T2_1/T2_2/T2_3 follows this shape:

```lean
obtain ⟨x, hPxQ, hRxS⟩ := inner_pasch ... h₁ h₂
have hPx : P = x := between_identity P x hPxQ  -- collapses Bet P x P
rw [← hPx] at hRxS                              -- substitute
exact hRxS  -- (possibly with between_symmetry)
```

It's worth abstracting as a small helper or aesop pattern.

**2. `by_cases` (via `point_equality_decidability`) unlocks T2_3.**
`between_exchange2` is the canonical "split on B = C" lemma — once
done, `outer_transitivity_between` and `between_exchange4` fall out
by symmetry one-liners.

**3. `Iff.rfl` works for `BetS` because `BetS` *is* the rhs.** Same
trick will work for many `BetSEq`-style "the def equals its body"
lemmas — `Reach`, `OutCircle`, etc.

### Updated Phase 0 numbers

- **451** signature-typed theorems in `Tarski_dev/Ch02–Ch09`
- **38** now proved (30 prior Ch02 + 13 Ch04_col + 25 Ch03_bet,
  minus 30 double-counted that were already done in Ch02_cong before
  Phase 0 started)  → **actually 38 new from Phase 0 sweeps**
- **413** still `sorry`
- **0 errors**, 281 build jobs

Phase 0 proved coverage now: **~8.4%** if you count Ch02 prior work,
or **~6%** for just the Phase 0 sweep work to date.

### Extrapolation refresh

Ch04_col hit 81%, Ch03_bet hit 86%. The pattern is consistent:
**80–90% of permutation/symmetry/triviality-heavy chapters close**
with the cascade. Updating estimates:

> **⚠️ Correction — see "Honest aesop experiment" below.** The above
> kill-rate numbers attributed too much credit to aesop. When the
> proofs were re-examined, almost all of them were actually hand
> translations of the Coq proofs into Lean tactic mode; only a small
> minority were closed by aesop unaided. The honest measurement below
> tells a different story.

| Chapter | Expected kill rate | Lemmas | Est. proved |
|---|---:|---:|---:|
| Ch02_cong | (already done) | 30 | 30 |
| Ch03_bet | (done — 86%) | 29 | 25 |
| Ch04_col + Ch04_cong_bet | 81% + ? | 22 | 18 |
| Ch05_bet_le | ~70% (more structural) | 66 | ~46 |
| Ch06_out_lines | ~70% | 53 | ~37 |
| Ch07_midpoint | ~60% (existential proofs) | 55 | ~33 |
| Ch08_orthogonality | ~50% (heavy structure) | 94 | ~47 |
| Ch09_plane | ~40% (TS/OS reasoning) | 109 | ~44 |
| **Projected total** | | **451** | **~280** |

That's **~62% projected proved coverage** of Phase 0 after sweeping
all chapters, up from the original 35–45% estimate. The pilot data
is more optimistic than the prior guess.

## Honest aesop experiment — Ch05_bet_le

The earlier numbers were soft. To actually measure what `aesop` can
do *unaided* (no Coq-proof reading, no hand-written tactic chain), I
ran a clean controlled experiment on `Ch05_bet_le` — 66 lemmas, never
touched by hand.

### Setup

1. Tagged **21 Cong permutation lemmas** in `Ch02_cong.lean` with
   `@[aesop safe forward]` or `@[aesop safe]` — full Cong permutation
   ruleset.
2. `Ch03_bet`'s `between_symmetry`, `between_trivial`, `between_trivial2`,
   `bet_col` already tagged from the prior session.
3. Replaced every `:= sorry` in `Ch05_bet_le.lean` with three different
   aesop attempts, one per pass. After each pass: build, count failures,
   restore.

### Pass 1 — pure `by aesop`

```lean
theorem l5_1 ... := by aesop
-- (repeated for all 66 lemmas)
```

**Result: 66/66 lemmas failed.** Pure aesop closed nothing. Errors
were either `tactic 'aesop' failed, made no progress` (aesop couldn't
match) or `unsolved goals` (aesop did *something* but didn't close).

### Pass 2 — `by (try unfold Le Lt Ge Gt ...); aesop`

```lean
theorem l5_1 ... := by
  (try unfold Le Lt Ge Gt Col Bet_4 BetS Out Midpoint at *)
  aesop
```

**Result: 66/66 lemmas failed.** Unfolding the structural defs first
didn't help — aesop still couldn't bridge the gap between the unfolded
goal (which mentions `∃ E, Bet ... ∧ Cong ...`) and the available
permutation lemmas.

### Pass 3 — `by intros; (try unfold); aesop`

Same wrapper plus explicit `intros` to discharge any leading binders.
**Result: 66/66 lemmas failed.** Same failure modes.

### What this means

**On a fresh chapter that needs real geometric construction
(segment_construction, inner_pasch, between_identity chains), aesop on
its own closes 0%.**

The 81% / 86% kill rates I reported for Ch04_col and Ch03_bet were
*not* aesop achievements. They were hand-translated Coq proofs. Of
38 lemmas reported as "closed by aesop" across those two chapters,
the breakdown is actually:

| Method | Ch04_col | Ch03_bet | Total |
|---|---:|---:|---:|
| Genuinely closed by aesop | 3 | 0 | **3** |
| Hand term-mode proof | 8 | 8 | 16 |
| Hand tactic-mode translation of Coq proof | 2 | 16 | 18 |
| `Iff.rfl` / `:= h` direct | 0 | 1 | 1 |
| **Total** | **13** | **25** | **38** |

So real aesop contribution to Phase 0 proofs to date: **3 of 38 = 8%.**

### Why aesop underperformed expectations

1. **GeoCoq's lemmas need real proof construction.** Most lemmas
   chain `segment_construction` + `inner_pasch` + `between_identity`.
   Aesop's safe rules don't construct existentials this way — it
   needs to *witness* an `E` and apply a complex axiom, not just
   propagate hypotheses through permutations.

2. **Forward rules don't fire on goal disjuncts.** A goal of
   `Bet A C D ∨ Bet A D C` doesn't trigger `between_symmetry`'s
   forward rule because there's no `Bet _ _ _` *hypothesis* yet.
   The hypothesis only appears after `rcases h with h | h | h`.

3. **`safe` rules are conservative.** Aesop only uses `safe` rules
   that won't accidentally undo themselves. Many useful chains
   (e.g. constructing a midpoint witness, then proving Cong) require
   `unsafe` rules with backtracking, which aesop's default
   configuration doesn't aggressively explore.

4. **Ch02's `Cong`-permutation tag set isn't even useful in Ch05.**
   Ch05 lemmas mostly talk about `Le`/`Lt`, which unfold to
   `∃ E, Bet C E D ∧ Cong A B C E`. The Cong permutations are about
   reordering args of `Cong`, which doesn't help when the goal is
   "find a witness E."

### What aesop is actually good for

- **Pure permutation goals** (`unfold X; tauto` or
  `unfold X; rcases; aesop`). About 5–10 lemmas per chapter.
- **Trivial wrappers** where the goal is `Cong A B B A` and a tagged
  `cong_pseudo_reflexivity` matches by unification.
- **`Iff.rfl` cases** where a `def`'s body literally equals the rhs.

These are real wins but represent a much smaller slice than my
earlier extrapolation suggested.

### Revised projection for Phase 0

| Bucket | Approx count in Phase 0 (438 sorries) | Aesop kill rate |
|---|---:|---:|
| Pure permutation lemmas | ~50 | **~80%** |
| Iff-rfl / def-unfolds | ~30 | **~95%** |
| Construction / Pasch / existential | ~300 | **~0%** |
| Decidability cases | ~30 | **~30%** |
| Other | ~28 | **~10%** |

Weighted estimate: **~12–18% real automatic kill rate** with the
current ruleset. That's the honest number to plan against. The other
80%+ of proofs need hand translation from Coq.

### Implication for the plan

The aesop cascade is **useful but not a multiplier**. It saves time
on the 50–80 lemmas across Phase 0 that match its sweet spot, but it
won't carry the project. The dominant cost remains hand-translating
Coq proofs into Lean tactic mode, at roughly the pace observed in
Ch03_bet (25 lemmas in one session of focused work).

What would actually multiply aesop's value:

1. **Custom `RuleSet` per file type** — e.g. for the "construct E
   via segment_construction, then apply five_segment" pattern,
   register a multi-step macro as a single aesop rule.
2. **`unsafe` rules with priorities** — let aesop try
   `segment_construction A B C D` to introduce a witness when the
   goal is `∃ E, Bet A B E ∧ Cong B E C D`. This needs careful tuning
   to avoid loops.
3. **`LeanHammer` integration** — first-order ATPs (Vampire, E) can
   handle the existential construction patterns aesop punts on. The
   setup tax (~30s per call) is worth it for the residual 300
   structural lemmas.

These are real next-phase research questions, not just configuration
tweaks. Not in scope for the current Phase 0.
