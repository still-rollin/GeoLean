# `lean-lsp-mcp` error log

Every point in the translation work where `lean-lsp-mcp` (the Lean LSP
bridge) returned `success: false` or otherwise blocked progress, plus
the diagnosis and the fix that worked.

The point of recording these is so the same kind of failure is recognised
faster next time, and so the methodology section of any write-up has
real evidence behind claims like "we hit typeclass-synthesis issues at
deep `extends`."

---

## 1. Looping `simp` set on `add_0_r` (demo, prior session)

**Where:** translation of `theories/Axioms/rocq_demo.v`, theorem
`add_0_r : ∀ n : ℕ, n + 0 = n`.

**Tool that returned the error:** `lean_diagnostic_messages` (after
writing the snippet).

**Error message:** `Possibly looping simp theorem: Nat.add_succ`.

**Root cause:** First attempt used
`induction n with | zero => rfl | succ n ih => simp [Nat.add_succ, ih]`.
But `n + 0 = n` is **definitionally true** on `Nat` in Lean — `Nat.add`
is defined by recursion on the *second* argument, so `n + 0` reduces to
`n` by `rfl`. Trying to nudge it with `simp [Nat.add_succ]` introduces
the wrong simp lemma and triggers a loop warning.

**Fix:** Replace the whole proof with `rfl`. One token.

**Lesson:** When a Coq proof goes through induction, the Lean
equivalent might collapse to `rfl` because of differing definitional
unfolding. Try the trivial tactic first.

---

## 2. Circle-typed argument fails typeclass synthesis at 2-deep `extends`

**Where:**
[Euclidean/Axioms.lean](../lean/geocoq_translate/GeocoqTranslate/Euclidean/Axioms.lean),
inside `class euclidean_neutral_ruler_compass`'s `where`-block, at the
call sites `euclidean_neutral_basis.OnCirc X K`,
`euclidean_neutral_basis.InCirc B K`, etc. inside `postulate_line_circle`
and `postulate_circle_circle`.

**Tool that returned the error:** `lean_diagnostic_messages`,
`success: false`.

**Error message (verbatim):**
```
Application type mismatch: The argument
  K
has type
  Circle
but is expected to have type
  euclidean_neutral_basis.Circle (?m.60 C D F G J K P Q R S)
in the application
  euclidean_neutral_basis.OnCirc X K
```

Plus two cascading errors at the *following* class declarations
(`euclidean_neutral_ruler_compass`, `euclidean_euclidean`) of the form
`` `sorryAx` is not a structure ``, because the failed elaboration
left the prior class as `sorry`.

**Root cause:** `euclidean_neutral_ruler_compass extends euclidean_neutral`,
which itself `extends euclidean_neutral_basis`. So inside the ruler-compass
`where`-block, the instance `[euclidean_neutral_basis Point]` would have
to be found by typeclass synthesis chaining through *two* `extends`
projections. Lean's synthesis didn't chain through both levels — the
instance metavariable stayed unsolved, and the dependent argument
`K : self.Circle` couldn't be unified against the unsolved type.

The same pattern *worked* one level shallower (inside
`euclidean_neutral`'s own `where`-block, e.g. `axiom_circle_center_radius`),
where only one `extends` projection separates the call site from the
basis class.

**Failed fix attempt:** Changed the derived `def`s
(`OnCirc`, `InCirc`, `OutCirc`) to `abbrev`, hoping reducibility would
let Lean unfold the type and unify. No change to the error.

**Working fix:** Force typeclass synthesis to run at the call site by
using explicit `@`-application with `Point _`:
```lean
@euclidean_neutral_basis.OnCirc Point _ X K
```
Applied to every `InCirc` / `OutCirc` / `OnCirc` call inside
`postulate_line_circle` and `postulate_circle_circle`. The shallower
call in `axiom_circle_center_radius` was left as the plain dotted form.

**Lesson:** Two-level `extends` + dependent argument type from the
grandparent class = use `@Parent.method Type _ …`. Don't waste time on
`abbrev` first.

---

## 3. Lean file at unexpected path → LSP can't find it

**Where:** Hilbert translation. Wrote the file using
`Write(file_path="/Users/.../GeocoqTranslate/Hilbert/Axioms.lean")`.
Then queried `lean_diagnostic_messages` on that exact path.

**Tool that returned the error:** `lean_diagnostic_messages`,
`success: false`.

**Error message:**
```
Invalid Lean file path: '/Users/.../GeocoqTranslate/Hilbert/Axioms.lean'
not found in any Lean project (no lean-toolchain ancestor or
file does not exist)
```

**Root cause:** Some tooling on the path (Write tool, IDE save hook, or
similar) silently renamed the new file from `Hilbert/Axioms.lean` to
`Hilbert/Hilbert_Axioms.lean`. The LSP query went to the requested
path, found nothing, and bailed out. The exact same renaming had
already happened to the existing Tarski and Euclidean axiom files
between sessions — they had become `Tarski/Tarski_Axioms.lean` and
`Euclidean/Euclidean_Axioms.lean`, which broke the subsequent
`lean_build` (see §5).

**Working fix:** `mv Hilbert/Hilbert_Axioms.lean Hilbert/Axioms.lean`
(and the analogous renames for Tarski and Euclidean). After the moves,
`lean_diagnostic_messages` returned clean and `lean_build` succeeded.

**Lesson:** If the LSP says a freshly-written file isn't found, check
the actual on-disk filename before assuming a write failed.

---

## 4. Plane-typed argument fails typeclass synthesis at 1-deep `extends`

**Where:**
[Hilbert/Axioms.lean](../lean/geocoq_translate/GeocoqTranslate/Hilbert/Axioms.lean)
line 100 (axiom `line_on_plane` inside `Hilbert_neutral_dimensionless`),
calling `Hilbert_neutral_basis.IncidLP l p`.

**Tool that returned the error:** `lean_diagnostic_messages`,
`success: false`.

**Error message (verbatim):**
```
Application type mismatch: The argument
  p
has type
  Plane
but is expected to have type
  Hilbert_neutral_basis.Plane (?m.40 A B l p)
in the application
  Hilbert_neutral_basis.IncidLP ?m.38 p
```

Plus cascading errors at subsequent class declarations
(`Hilbert_neutral_2D`, `Hilbert_neutral_3D`,
`Hilbert_neutral_dimensionless` itself referenced from
`namespace Hilbert_euclidean`).

**Root cause:** Same flavour as §2, but at only **one** `extends` level
deep — `Hilbert_neutral_dimensionless extends Hilbert_neutral_basis`,
and the call sits inside that where-block. Unlike Euclidean (where the
1-deep call to `OnCirc` worked), here it failed.

Difference from the Euclidean case: `IncidLP l p` has *two* dependent
arguments (`l : self.Line`, `p : self.Plane`), both from the basis
class. `OnCirc B J` only had one (`J : self.Circle`; `B : Point` is a
non-dependent direct class param). With two dependent args, Lean's
synthesizer had two metavariables to solve simultaneously against
locally-bound `Line`/`Plane` types, and it couldn't.

**Working fix:** Same as §2 — explicit `@` form:
```lean
@Hilbert_neutral_basis.IncidLP Point _ l p
```

**Lesson:** The 1-vs-2-deep heuristic from §2 was incomplete. The
real rule is: as soon as a derived def has **a dependent argument
type from the basis class**, default to `@Parent.method Type _ …` no
matter how shallow the `extends` chain — it's never wrong, and you'll
skip a round of debugging.

---

## 5. Second-order error from the same fix — `pasch` axiom

**Where:**
[Hilbert/Axioms.lean](../lean/geocoq_translate/GeocoqTranslate/Hilbert/Axioms.lean)
line 111, axiom `pasch`, references `Hilbert_neutral_basis.IncidLP l p`
and `Hilbert_neutral_basis.cut l A B`.

**Tool that returned the error:** PostToolUse hook diagnostic after the
Edit that fixed `line_on_plane`.

**Error message:** Identical shape to §4 (Application type mismatch on
`p` of type `Plane`).

**Root cause:** Lean had been reporting only the *first* occurrence of
the synthesis failure per file. Once §4 was fixed, the same bug at the
next call site (`pasch`) became visible. The class body had multiple
Plane/Line-dependent derived-def calls and each one needed the same
treatment.

**Working fix:** Same `@`-form, applied to **both** the `IncidLP` call
and the two `cut` calls inside `pasch`:
```lean
@Hilbert_neutral_basis.IncidLP Point _ l p →
¬ IncidL C l →
@Hilbert_neutral_basis.cut Point _ l A B →
@Hilbert_neutral_basis.cut Point _ l A C ∨
@Hilbert_neutral_basis.cut Point _ l B C
```

After this edit, `lean_diagnostic_messages` returned `success: true`
with no errors.

**Lesson:** When fixing a synthesis error, eagerly apply the same fix
to all sibling call sites in the same class body — don't wait for Lean
to surface them one at a time.

---

## 6. `lean_build` failure: cascading missing-file from §3

**Where:** project-level `lake build` after wiring
`import «GeocoqTranslate».Hilbert.Axioms` into the library root.

**Tool that returned the error:** `lean_build`, `success: false`.

**Error message:**
```
error: no such file or directory (error code: 4294967294)
  file: /Users/.../GeocoqTranslate/Tarski/Axioms.lean
Some required targets logged failures:
- job computation
error: build failed
```

**Root cause:** The Hilbert file got renamed correctly (§3), but the
older Tarski and Euclidean files had been silently renamed to
`Tarski/Tarski_Axioms.lean` and `Euclidean/Euclidean_Axioms.lean`
between sessions. The library root still imported them under their
original names, so Lake couldn't find them.

**Working fix:** Rename the existing files back:
```bash
mv Tarski/Tarski_Axioms.lean   Tarski/Axioms.lean
mv Euclidean/Euclidean_Axioms.lean Euclidean/Axioms.lean
```
After that, `lean_build` reported 7/7 jobs successful (all three
axiom modules + root).

**Lesson:** Renaming-by-tooling is sticky — once a file gets the wrong
name, the bad name persists across sessions until manually fixed.
Worth running a `find . -name "*.lean"` sanity check before any
multi-file rebuild.

---

## 7. Auto-rename recurs (Tarski + Euclidean + Hilbert, again)

**Where:** start of Ch02_cong work. Before writing the new file, I went
to read [Tarski/Axioms.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski/Axioms.lean).

**Tool that returned the error:** `Read` returned "File does not exist".

**Root cause:** The same `Foo/Axioms.lean` → `Foo/Foo_Axioms.lean`
renaming from §3 / §6 had happened again between sessions to all three
files (Tarski, Euclidean, Hilbert). The IDE notification confirmed:
the user's IDE had opened `Tarski/Tarski_Axioms.lean`, so whatever does
the renaming was active again.

**Working fix:** Same as §6 — bulk `mv` back:
```bash
mv Tarski/Tarski_Axioms.lean       Tarski/Axioms.lean
mv Euclidean/Euclidean_Axioms.lean Euclidean/Axioms.lean
mv Hilbert/Hilbert_Axioms.lean     Hilbert/Axioms.lean
```

**Lesson confirmed across multiple sessions:** the rename is
**persistent and recurring**, not a one-shot accident. It only seems
to hit files named exactly `Axioms.lean`; the new `Ch02_cong.lean` and
`Definitions.lean` written this session were left alone. Cause still
unknown (no Claude hook, no VS Code task that obviously does this).
Until we identify and disable the source, run a `find` check at the
start of each session.

---

## 8. Term-mode application missing explicit Tpoint args

**Where:** [Tarski_dev/Ch02_cong.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Ch02_cong.lean),
the very first lemma `cong_reflexivity`.

**Tool that returned the error:** `lean_diagnostic_messages`,
`success: false`.

**Error message:**
```
Application type mismatch: The argument
  cong_pseudo_reflexivity B A
has type
  Cong B A A B
of sort `Prop` but is expected to have type
  Tpoint
of sort `Type` in the application
  cong_inner_transitivity B A A B (cong_pseudo_reflexivity B A)
```

**Root cause:** First attempt was a literal port of the Coq:
```lean
cong_inner_transitivity B A A B
  (cong_pseudo_reflexivity B A)
  (cong_pseudo_reflexivity B A)
```
mirroring Coq's `apply (cong_inner_transitivity B A A B); apply
cong_pseudo_reflexivity`. But `cong_inner_transitivity` in our Lean
class has all six points as **explicit** arguments:
```
cong_inner_transitivity :
  ∀ A B C D E F : Tpoint, Cong A B C D → Cong A B E F → Cong C D E F
```
The Coq `apply` was filling `E` and `F` from the goal during
unification. Lean term-mode does not — it consumes positional arguments
in order, sees `(cong_pseudo_reflexivity B A) : Cong B A A B` where it
expected `E : Tpoint`, and gives the mismatch.

**Working fix:** Add the missing two explicit Tpoint args between the
four points and the two hypotheses:
```lean
cong_inner_transitivity B A A B A B
  (cong_pseudo_reflexivity B A)
  (cong_pseudo_reflexivity B A)
```

**Lesson:** Coq's `apply` is bidirectional (uses goal to infer remaining
universally-quantified args); Lean term-mode is left-to-right (consumes
positionals in order). When porting `apply (Lemma a b c); …` to Lean
term-mode, always check the lemma's full signature — Coq may be
filling more args from the goal than the surface syntax suggests.

---

## 9. Coq's `Cong` hint tactic silently inserts `cong_symmetry`

**Where:** [Tarski_dev/Ch02_cong.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Ch02_cong.lean),
the `bet_cong3` lemma.

**Tool that returned the error:** `lean_build`, `success: false`.

**Error message:**
```
error: GeocoqTranslate/Tarski_dev/Ch02_cong.lean:182:47:
Application type mismatch: The argument
  hCong
has type
  Cong B' x B C
but is expected to have type
  Cong B C B' x
in the application
  l2_11 A B C A' B' x h1 hBet h2 hCong
```

**Root cause:** The Coq proof is:
```coq
assert (Cong A C A' x).
  eapply l2_11.
    apply H.    (* Bet A B C *)
    apply H1.   (* Bet A' B' x *)
    assumption. (* Cong A B A' B' *)
  Cong.         (* fourth premise *)
```
The fourth premise the Coq `Cong` tactic supplies is `Cong B C B' x`.
What's actually in scope (from `segment_construction A' B' B C`) is
`Cong B' x B C` — the symmetric. The `Cong` tactic searches the `cong`
hint database, finds `cong_symmetry`, and applies it silently.

In Lean, there's no `Cong` tactic. `l2_11` requires the fourth premise
to have *exactly* type `Cong B C B' x`, and `cong_symmetry` has to be
inserted explicitly.

**Working fix:** Bind the symmetric form before using it:
```lean
have hBCBx : Cong B C B' x := cong_symmetry B' x B C hCong
exact ⟨x, h2, l2_11 A B C A' B' x h1 hBet h2 hBCBx, hBCBx⟩
```

**Lesson — this is the canonical proof-translation friction.** Coq's
hint databases (`cong`, `cong3`, ...) make permutation lemmas invisible
in the source proof. Every `apply` or `eauto using …` step that the
tactic resolves through the database hides an `apply cong_symmetry` or
`apply cong_left_commutativity`. Lean equivalents (`aesop` with custom
hint sets) exist, but cost more elaboration time. For now, default to
"insert the explicit `cong_*` permutation by hand". Later chapters
where Coq proofs lean heavily on `Cong` will translate at ~5× the
length of the source.

---

## 13. `by_contra` tactic not available

**Where:** [lemma_extensionunique.lean](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/Lemmas/lemma_extensionunique.lean),
trying to prove `E = F` by assuming `E ≠ F` and deriving contradiction.

**Tool that returned the error:** `lean_build`, `success: false`.

**Error message:**
```
GeocoqTranslate/Elements/OriginalProofs/Lemmas/lemma_extensionunique.lean:25:3:
unknown tactic
```
plus "unsolved goals" for the enclosing `by` block.

**Root cause:** `by_contra` is a Mathlib tactic
(`Mathlib.Tactic.ByContra`). Our project depends on Mathlib via Lake
(`require mathlib from git`), but none of our files transitively
import any Mathlib module — `Euclidean/Axioms.lean` and the lemma
files only import each other and core Lean. So `by_contra` isn't in
scope, even though `obtain`, `rcases`, and `subst` (which are now in
Lean core) are.

**Working fix:** swap `by_contra hEF` for the equivalent core-Lean
idiom:
```lean
apply Classical.byContradiction
intro hEF
-- goal is now False, hEF : ¬(E = F) in scope
```

`Classical.byContradiction : ¬¬p → p` is in `Init.Logic` (Lean core);
no extra imports needed.

**Lesson:** the line between Lean-core tactics and Mathlib tactics has
moved several times. When a tactic is "unknown" in a Mathlib-using
project, check whether the tactic in particular requires an explicit
Mathlib import even if Mathlib is a project-level dependency. The
core-Lean equivalents (`Classical.byContradiction`, `Or.elim` on
`Classical.em`, `Decidable.em` for decidable cases) are usually one
line longer but always available.

---

## Summary table

| # | What returned `success: false` | Root cause | Fix |
|---|---|---|---|
| 1 | `lean_diagnostic_messages` | Wrong simp lemma triggered loop; goal was `rfl` | Replace proof with `rfl` |
| 2 | `lean_diagnostic_messages` | TC synth doesn't chain 2 `extends` with dependent arg | `@Parent.method Type _ …` |
| 3 | `lean_diagnostic_messages` | File on disk not at expected path | `mv` to correct path |
| 4 | `lean_diagnostic_messages` | Same as §2 but at 1-deep with **two** dependent args | Same `@`-fix |
| 5 | `lean_diagnostic_messages` | Lean reports one synth error at a time; siblings still broken | Apply `@`-fix to all siblings together |
| 6 | `lean_build` | Renamed files from §3-style mangling still wrong | `mv` all the affected files |
| 7 | `Read` (file does not exist) | Same auto-rename as §3/§6 recurred between sessions | Same `mv` fix; treat as recurring, sanity-check at session start |
| 8 | `lean_diagnostic_messages` | Coq `apply` infers explicit args from goal; Lean term-mode does not | Add the missing explicit Tpoint args |
| 9 | `lean_build` | Coq's `Cong` hint tactic silently inserts `cong_symmetry`; Lean does not | Bind the symmetry with `have …` and pass it explicitly |
| 10 | — (mentor review, not LSP) | ~~Two-class split + `@`-workaround was solving a non-problem~~ — **retracted by §11** | (no longer applies; rewrite reverted) |
| 11 | `lean_build` | Default-valued class field is opaque outside the class; also overridable (Julien's review) | Revert §10 — go back to two-class split with namespaced `def`s |
| 12 | `lean_build` | Plain `def` is semi-reducible; anonymous constructor doesn't auto-unfold the body | `show <unfolded body>` before `exact ⟨…⟩`, or mark `@[reducible]` |
| 13 | `lean_build` | `by_contra` tactic not in scope (project doesn't transitively import Mathlib.Tactic) | Use `apply Classical.byContradiction; intro h` instead |
| 14 | `lean_diagnostic_messages` (×4 sites) | Misread `lemma_congruencesymmetric`'s positional args as input-positions when they name output-positions | Match positional args to the conclusion shape, not the hypothesis |
| 15 | `lean_diagnostic_messages` | `obtain ⟨a,b,c⟩` bindings depended on Lean's conjunction order, which differed from Coq convention | Read the `def` body in the Lean port before destructuring |
| 16 | `lean_diagnostic_messages` | `subst h` removed the wrong variable for `h : C = A` (later-introduced var goes) | Use `rw [h] at <hyp>` for two-var equations |
| 17 | `lean_diagnostic_messages` | `@[aesop norm unfold]` syntax not recognized by current Aesop | Use `@[simp]` — aesop runs simp during normalization |

Six categories of root cause:
- **One issue (1)** — Lean idiom mismatch, fix by knowing Lean.
- **Three issues (2, 4, 5)** — Typeclass synthesis through `extends`
  with dependent argument types. The `@Parent.method Type _ …`
  workaround works, but these failures only arose because of the
  basis-class + namespaced-`def` split used in early translations.
  **No longer applies after the architecture change in §10** — keep
  these here as historical reference.
- **Three issues (3, 6, 7)** — Tooling auto-renames `Foo/Axioms.lean`
  → `Foo/Foo_Axioms.lean`. Recurring across sessions. Cause still
  unknown; `mv` is the workaround.
- **Two issues (8, 9)** — Coq tactics (`apply` with unification,
  `Cong` with hint DB) fill in arguments that Lean term-mode cannot.
  General lesson: every Coq `apply Lemma a b` or `auto with X` step
  may hide additional explicit args or permutation lemmas that have
  to be supplied by hand in Lean.
- **Three issues (14, 15, 16)** — Translator-memory errors on positional
  args, conjunction-destructure order, and `subst` direction. Each is
  one-shot recoverable from the LSP error message, but the recurrence
  across multiple sites (especially §14 across four files) is what made
  the `geolean_oracle` MCP investment worthwhile — it pre-resolves arg
  orders from Coq's `Show Proof.` so the guessing loop disappears.
- **One issue (17)** — Aesop attribute-syntax version drift. Fall back
  to `@[simp]` when the bespoke syntax doesn't parse.

---

## 10. ~~Retrospective: §2 / §4 / §5 were workarounds for a non-issue~~ — itself retracted, see §11

**Original claim (now incorrect):** Lean's default-valued class fields
were proposed as a cleaner replacement for the basis-class +
namespaced-`def` split, on the grounds that they let the axioms
reference derived predicates without the `@Parent.method Type _ …`
workaround.

**Test that initially supported the claim:**
```lean
class Base (P : Type) where
  prim : P → P → P → P → Prop
  Circle : Type
  CI : Circle → P → P → P → Prop
  OnCirc (b : P) (j : Circle) : Prop :=
    ∃ x y u : P, CI j u x y ∧ prim u b x y

class Outer (P : Type) extends … extends Base P where
  ax : ∀ (b : P) (j : Circle), OnCirc b j → True
```
This elaborates. The axiom statement compiles.

**What §11 then found** is that this elaboration only proves that the
*type* `OnCirc b j` is well-formed — not that *values* of that type
can be constructed in downstream proofs. And independently, Julien
flagged that the default-value form lets instances override the
predicate. Both push the same way: revert. See §11.

The work products from this entry (the single-class rewrites of
`Euclidean/Axioms.lean` and `Hilbert/Axioms.lean`) were undone. The
files are back to the two-class-split form documented in §2 / §4 / §5.

---

## 11. The default-valued-field approach is wrong twice over

**Where:** while starting on Proposition 1 of Euclid, in
[lemma_localextension.lean](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/Lemmas/lemma_localextension.lean),
trying to construct an `InCirc B J` value to feed `postulate_line_circle`.

**Tool that returned the error:** `lean_build`, `success: false`.

**Error message:**
```
Invalid ⟨...⟩ notation: The expected type
  inst✝.toeuclidean_neutral.14 B J
is not an inductive type
```

**Root cause (proof side):** in the single-class form proposed in §10,
`InCirc` is a default-valued class field. From outside the class, a
field projection is opaque — Lean treats `inst.InCirc B J` as a black-
box `Prop`, *not* as `∃ X Y U V W, …`. The anonymous-constructor
notation `⟨…⟩` fails because Lean can't see the inductive structure
behind the field. Verified that none of the obvious workarounds help:

| Attempt | Result |
|---|---|
| `unfold InCirc` | "Unknown identifier" / no reduction on field projection |
| `attribute [reducible] euclidean_neutral.InCirc` | No effect on field-projection unfolding |
| `show ∃ X Y U V W, …` | Type mismatch — not definitionally equal to the field |
| Direct `⟨…⟩` | "is not an inductive type" |

**Independent issue (Julien's review, soundness side):** even if
construction worked, an instance can override `InCirc` by giving its
own value. That breaks the cross-system equivalence theorems
(Tarski ≡ Euclid ≡ Hilbert) — those are proved against the canonical
definition, and an instance with `Col := fun _ _ _ => True` would
satisfy "Euclid" without satisfying Tarski.

**Both concerns point at the same fix.** Roll the §10 rewrite back to
the §2 / §4 / §5 two-class split: primitives in
`euclidean_neutral_basis`, derived predicates as plain `def`s in the
surrounding namespace (parameterised by the typeclass instance), axioms
in `euclidean_neutral` extending the basis. Real `def`s are
unoverridable (semantic correctness) and respond to `show ∃ …`
(constructibility in proofs).

**Working fix in `lemma_localextension`:**
```lean
have hInCirc : InCirc B J := by
  show ∃ X Y U V W : Point,
    CI J U V W ∧ (B = U ∨ (BetS U Y X ∧ Cong U X V W ∧ Cong U B U Y))
  exact ⟨B, B, B, B, Q, hCI, Or.inl rfl⟩
```

`show ∃ …` works on a plain `def` because `def` is semi-reducible —
Lean unfolds the body during type-check when the user asks for a
specific shape. It does **not** work on a class field projection,
which is what made the single-class form a dead end.

**Lesson — twofold:**
1. *Test the proof side, not just the axiom side.* The §10 test verified
   that the axiom statements *elaborate* (the type is well-formed). It
   did not verify that values of those types are *constructible* in
   downstream proofs. That's a separate question and the binding one
   for a library that's intended to be reasoned on top of.
2. *Listen carefully to mentor concerns.* Julien's override worry
   wasn't just style — it was about a class of theorems (the cross-
   system equivalences) silently becoming unsound. The two arguments
   converged on the same answer; either alone would have justified
   the revert.

After the revert, `lake build` reports 14 jobs successful (axioms +
Ch02 + 5 Element lemmas).

---

## 12. `show ∃ …` needed to construct values of namespaced-`def` predicates

**Where:** [lemma_localextension.lean](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/Lemmas/lemma_localextension.lean),
constructing `hInCirc : InCirc B J`.

**Tool that returned the error:** `lean_build`, `success: false`.
First attempt — naïve anonymous constructor — failed with the same
"is not an inductive type" message as §11, but for a *different*
reason: even after reverting to the two-class form, plain `def` is
**semi-reducible**, not reducible. The anonymous constructor doesn't
auto-unfold semi-reducible definitions.

**Working fix:** ascribe the unfolded type explicitly with `show ∃ …`,
then `exact ⟨…⟩`:

```lean
have hInCirc : InCirc B J := by
  show ∃ X Y U V W : Point,
    CI J U V W ∧ (B = U ∨ (BetS U Y X ∧ Cong U X V W ∧ Cong U B U Y))
  exact ⟨B, B, B, B, Q, hCI, Or.inl rfl⟩
```

`show` accepts any type that's definitionally equal to the goal. For
a plain `def`, "definitionally equal" includes reducing the `def`
body — Lean does this on demand. So `show <unfolded body>` succeeds
where the bare `⟨…⟩` doesn't.

**Alternative:** mark the `def` `@[reducible]` (equivalent to `abbrev`)
to make Lean auto-unfold during elaboration. Skipped here because
(a) Ayaan committed to plain `def` in the email exchange with Julien,
and (b) explicit `show ∃ …` documents the unfolded form at the use
site, which is useful when reading the proof.

**Lesson:** when porting Coq proofs that construct values of
`Definition`-typed predicates, expect to need either `show <body>` or
`unfold <name>` before the anonymous constructor. Coq's `Definition`s
are fully transparent (reducible-by-default); Lean's plain `def`s are
not. The two-line cost is small but it adds up across many proofs.

---

## 14. Argument-order confusion on `lemma_congruencesymmetric` (recurring)

**Where:**
- [lemma_doublereverse.lean](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/Lemmas/lemma_doublereverse.lean) line 25,
- [lemma_differenceofparts.lean](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/Lemmas/lemma_differenceofparts.lean) lines 38, 62,
- [proposition_02.lean](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/proposition_02.lean) lines 60, 61, 73, 74.

**Tool that returned the error:** `lean_diagnostic_messages` / `lean_build`,
`success: false`. Same shape across all sites — `Application type mismatch`
on the hypothesis argument.

**Concrete instance (from `lemma_doublereverse`):**
```
error: lemma_doublereverse.lean:25:66:
Application type mismatch: The argument
  h_BADC
has type
  Cong B A D C
but is expected to have type
  Cong C B D A
in the application
  lemma_congruencesymmetric D C B A h_BADC
```

**Root cause:** the lemma's actual signature is
```lean
lemma_congruencesymmetric (A B C D : Point) (h : Cong B C A D) : Cong A D B C
```
The four `Point` positional args name the *output* (`Cong A D B C`), not
the input. To produce `Cong D C B A` from `Cong B A D C`, the right call
is `lemma_congruencesymmetric D B A C h_BADC` — match the four positional
args **to the conclusion**, then the hypothesis is consumed in the order
`Cong B C A D` = `Cong B A D C`. Easy to misread the signature as
"input first" — the same mistake was made at four different sites this
session before the pattern clicked.

**Working fix:** read the signature as *target-first*. The `(A B C D)`
positional args correspond to the conclusion `Cong A D B C`, not to the
input. Same pattern applies to `lemma_congruenceflip`'s triple
projection — `(lemma_congruenceflip A B C D h).2.1` returns
`Cong B A C D`, so the four positional args are again target-positions.

**Lesson:** for any GeoCoq-style permutation lemma, the positional
arguments name **output positions**. Hovering on the lemma symbol in
VS Code shows the conclusion type immediately, which is the right
mental anchor. Don't try to remember the signature; look at it. (This
recurring failure is what motivated building the `geolean_oracle` MCP
server — Coq's `Show Proof.` records the resolved positional args
directly, eliminating the guess.)

---

## 15. `obtain ⟨a, b, c⟩` on `Cong_3` unfolds in non-obvious order

**Where:** [Tarski_dev/Ch04_col.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Ch04_col.lean)
line 110 (inside `l4_13`), destructuring the `Cong_3 A B C A' B' C'`
hypothesis.

**Tool that returned the error:** `lean_diagnostic_messages`,
`success: false`, after the first draft of the proof.

**Error message:**
```
Application type mismatch: The argument
  hBC
has type
  Cong A C A' C'
but is expected to have type
  Cong B C B' C'
in the application
  And.intro hBC
```

(Plus cascading mismatches at 5 other sites in the same `rcases` block.)

**Root cause:** I assumed `Cong_3 A B C A' B' C'` was
`Cong A B A' B' ∧ Cong B C B' C' ∧ Cong A C A' C'` and destructured as
`⟨hAB, hBC, hAC⟩`. The actual `def` in
[Tarski/Definitions.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski/Definitions.lean)
is `Cong A B A' B' ∧ Cong A C A' C' ∧ Cong B C B' C'`. So `obtain ⟨a, b, c⟩`
binds `b` to the `Cong A C` component, not the `Cong B C` one. The variable
names I picked (`hAB`, `hBC`, `hAC`) were a lie about the actual contents.

**Working fix:** rename the destructure bindings to match the def's
actual ordering — `obtain ⟨hAB, hAC, hBC⟩ := h₂` — and reorder every
constructor-style `⟨…⟩` that builds a `Cong_3`. The proof body itself
didn't need to change beyond the renaming.

**Lesson:** before destructuring a Coq-derived `def`, jump to its
definition and read the conjunction order *in the Lean port*. Coq
conventions (`Cong A B → Cong B C → Cong A C` as a natural traversal)
don't constrain the Lean translator, and minor reorderings during the
port can flip the binding order without changing the meaning.

---

## 16. `subst h` for `h : C = A` removes the unexpected variable

**Where:** [lemma_differenceofparts.lean](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/Lemmas/lemma_differenceofparts.lean)
line 45, inside the `B ≠ A` case, proving `C ≠ A` by contradiction.

**Tool that returned the error:** `lean_diagnostic_messages`,
`success: false`, immediately after writing the first draft.

**Error message:**
```
Unknown identifier `A`
```
at the `exact axiom_betweennessidentity A B h3` line — even though `A`
was in scope at the start of the proof.

**Root cause:** the proof draft was:
```lean
have hCA : C ≠ A := by
  intro hCAeq          -- hCAeq : C = A
  subst hCAeq
  exact axiom_betweennessidentity A B h3
```
`subst hCAeq` for `hCAeq : C = A` substitutes the *most-recently-introduced*
free variable. `A` was introduced earlier in the theorem signature
(as part of `(A B C a b c : Point)`), and `C` was introduced later, so
Lean substitutes `A := C` and removes `A` from scope. Goal becomes
`Bet C B C → False` and `A` is no longer an identifier in context.

**Working fix:** rewrite at the hypothesis instead of `subst`-ing:
```lean
have hCA : C ≠ A := by
  intro hCAeq
  rw [hCAeq] at h3
  exact axiom_betweennessidentity A B h3
```
`rw` is directional and only touches `h3` — `A` stays in scope.

**Lesson:** when an equation has variables on both sides, `subst` may
go either direction depending on introduction order; `rw [h] at <hyp>`
is unambiguous. Use `rw` when you only need to rewrite a single
hypothesis, especially if the equality involves two locally-bound
variables.

---

## 17. `@[aesop norm unfold]` attribute syntax rejected

**Where:** [Tarski/Definitions.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski/Definitions.lean)
lines 29 and 34, attempting to mark `Cong_3` and `Col` for aesop's
normalization step.

**Tool that returned the error:** `lean_diagnostic_messages`,
`success: false`, on save.

**Error message:**
```
unexpected identifier; expected ']'
```
at column 13 of `@[aesop norm unfold]`.

**Root cause:** the bare `@[aesop norm unfold]` form is not accepted
by the Aesop version pinned in our Mathlib. Without checking the exact
supported spelling (which would have required digging into Aesop's
attribute parser), the simplest workaround is to use `@[simp]` instead
— aesop's normalization step runs `simp`, so any rule tagged `@[simp]`
is picked up automatically.

**Working fix:** use `@[simp]`:
```lean
@[simp]
def Cong_3 (A B C A' B' C' : Tpoint) : Prop :=
  Cong A B A' B' ∧ Cong A C A' C' ∧ Cong B C B' C'

@[simp]
def Col (A B C : Tpoint) : Prop :=
  Bet A B C ∨ Bet B C A ∨ Bet C A B
```
Side-effect verified by `lean_build`: the project rebuilds 2974 jobs
cleanly with the `@[simp]` tags, and aesop now closes 2 of 3 cases of
`l4_13` unaided (where before the tagging it closed 0).

**Lesson:** if a specific aesop attribute syntax doesn't parse, fall
back to `@[simp]`. Aesop's normalizer runs `simp`, so `@[simp]` gives
most of the same effect for `def`-wrapped predicates without fighting
the attribute parser.
