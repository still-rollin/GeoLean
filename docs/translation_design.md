# Rocq → Lean 4 translation: approaches, design choices, results

Companion to [claude_mcp_workflow.md](claude_mcp_workflow.md). That doc covers
*how* Claude Code drives the two MCP servers; this doc covers *what got
translated and why it looks the way it does*.

## 1. Overall approach

Both `rocq-mcp` and `lean-lsp-mcp` are wired into Claude Code via
[../.mcp.json](../.mcp.json). The translation loop per Rocq item:

```
1. mcp__rocq-mcp__rocq_start         extract Rocq statement / class body
2. Claude writes Lean 4 directly     no separate LLM hop
3. mcp__lean-lsp-mcp__lean_run_code  compile snippet → diagnostics
   mcp__lean-lsp-mcp__lean_diagnostic_messages  diagnostics on on-disk file
   mcp__lean-lsp-mcp__lean_build     full Lake build when adding modules
4. On error: read diagnostic, rewrite, retry. Agent loop, no fixed attempt cap.
```

No Python orchestrator, no Gemini. Verification is real Lean compilation
end-to-end.

## 2. Cross-cutting design choices

These choices apply to every translation in this branch. Settled
in conversation with the user on the Tarski axioms; reused for Euclidean,
Hilbert, and the first `Tarski_dev` chapter.

| Choice | Decision | Rationale |
|---|---|---|
| **`Point` exposure** | `Type` parameter on the class, not a field | Idiomatic Lean. Downstream theorems write `variable (α : Type) [SomeAxioms α]`, multiple geometries can sit on the same carrier, and `Point` appears once in the class signature instead of being projected out everywhere. |
| **Class hierarchy** | `extends` rather than separate classes | `[Tarski_2D Point]` automatically provides the base axioms. Avoids the Rocq-style stack of three or four `[base]`, `[decidable]`, `[2D]` constraints at every use site. |
| **Naming** | Keep Rocq snake_case (`cong_pseudo_reflexivity`, `axiom_lower_dim`, ...) | One-to-one cross-reference with the source. The Lean-idiomatic `camelCase` rename would silently diverge as the source evolves. |
| **File granularity** | One Lean file per Rocq file | Mirrors the source. `tarski_axioms.v` → [Tarski/Axioms.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski/Axioms.lean); `Ch02_cong.v` → [Tarski_dev/Ch02_cong.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Ch02_cong.lean). All wired into [GeocoqTranslate.lean](../lean/geocoq_translate/GeocoqTranslate.lean) so `lake build` picks them up. |
| **In-class derived defs** | Translate as plain `def`s in a namespace, *outside* the axiom class. Structure: `class Foo_basis` (primitives) → `namespace Foo_basis` (derived `def`s, parameterised by `[Foo_basis Point]`) → `class Foo extends Foo_basis` (axioms, referencing derived defs by qualified name). | This mirrors Rocq's `Definition` semantics: the derived predicate has a fixed body and cannot be overridden by an instance. **An earlier rewrite tried Lean's default-valued-field syntax** (`name (args) : T := body` inside the class). That form is rejected for two reasons: (a) Julien flagged that an instance can *override* a default-value field, which would silently invalidate the cross-system equivalence theorems (Tarski ≡ Euclid ≡ Hilbert) — these hold only for the canonical definition of `Col` / `OnCirc` / etc. (b) Default-value fields are *opaque* from outside the class — values like `InCirc B J` cannot be constructed with the anonymous constructor `⟨…⟩` because Lean doesn't see the field as definitionally equal to its body. `unfold`, `@[reducible]`, and `show` were all tested; none unfold a field projection. Both concerns point at the same fix: use real `def`s in a namespace. Cost: the axiom class's where-block has to reference derived defs by qualified name (`euclidean_neutral_basis.nCol PA PB PC`), and a few deep-`extends` call sites need `@Foo_basis.method Point _ …` to force typeclass synthesis (documented in [lean_lsp_errors.md](lean_lsp_errors.md) §2/§4/§5). |
| **Proof style: term mode by default, tactic when destructuring** | Plain congruence chains as term-mode; case splits / `∃` destructuring / `subst` use `by`. | Term-mode mirrors Coq's `apply (cong_inner_transitivity B A A B)` more closely than tactic translations, and `lean_diagnostic_messages` gives sharper errors on bad term-mode terms. Tactic mode is unavoidable for `obtain` / `rcases` / `subst`. |

## 3. Per-file design

### 3.1 `theories/Axioms/rocq_demo.v` → demo

Five throwaway theorems (`add_0_r`, `add_comm`, `length_app`, `de_morgan`,
`exists_not_all`) used to validate the MCP loop end-to-end. Final consolidated
output:
[lean/geocoq_translate/GeocoqTranslate/Scratch.lean](../lean/geocoq_translate/GeocoqTranslate/Scratch.lean).

**Notable design move:** `add_0_r` (`∀ n, n + 0 = n`) collapses to `rfl`
in Lean — definitionally true on `Nat`. The first attempt used
`simp [Nat.add_succ, ih]`, which Lean's diagnostic flagged as a looping
simp set ("Possibly looping simp theorem: `Nat.add_succ`"). Replaced with
`rfl`. This is the only mid-translation repair; the other four compiled
first-try.

### 3.2 `theories/Axioms/tarski_axioms.v` → [Tarski/Axioms.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski/Axioms.lean)

Seven Rocq `Class`es → seven Lean `class`es, hierarchy via `extends`.

| Rocq class | Lean class | Adds |
|---|---|---|
| `Tarski_neutral_dimensionless` | same | `Bet`, `Cong`, 7 axioms, `PA`, `PB`, `PC`, `lower_dim` |
| `..._with_decidable_point_equality` | same | `point_equality_decidability` |
| `Tarski_2D` | same | `upper_dim` |
| `Tarski_3D` | same | `S1..S4`, `lower_dim_3`, `upper_dim_3` |
| `Tarski_euclidean` | same | `euclid` |
| `Tarski_ruler_and_compass` | same | `circle_circle_continuity` |
| `Tarski_continuous` | same | `continuity` (Dedekind-cut form) |

**No surprises.** Every axiom statement references only structural fields
(`Bet`, `Cong`) and the universally-quantified points. The translation
compiled clean on the first attempt.

### 3.3 `theories/Axioms/euclidean_axioms.v` → [Euclidean/Axioms.lean](../lean/geocoq_translate/GeocoqTranslate/Euclidean/Axioms.lean)

Four Rocq `Class`es. The Rocq `euclidean_neutral` class contains eight
derived predicates (`nCol`, `Col`, `Cong_3`, `TS`, `Triangle`, `OnCirc`,
`InCirc`, `OutCirc`) defined inline in its body and then referenced by
the axioms in the same class.

**Translation: two-class split.**

1. `class euclidean_neutral_basis (Point : Type)` — structural fields
   only: `Circle`, `Cong`, `BetS`, `CI`, `PA`, `PB`, `PC`.
2. `namespace euclidean_neutral_basis` — the eight derived predicates
   as plain `def`s, parameterised by `[euclidean_neutral_basis Point]`.
3. `class euclidean_neutral extends euclidean_neutral_basis Point` —
   the 17 axioms. Axioms reference derived defs by qualified name
   (`euclidean_neutral_basis.nCol PA PB PC`).
4. `euclidean_neutral_ruler_compass`, `euclidean_euclidean`, `area`
   chain on top via `extends`.

```lean
class euclidean_neutral_basis (Point : Type) where
  Circle : Type
  Cong : Point → Point → Point → Point → Prop
  BetS : Point → Point → Point → Prop
  CI : Circle → Point → Point → Point → Prop
  PA : Point ; PB : Point ; PC : Point

namespace euclidean_neutral_basis
variable {Point : Type} [self : euclidean_neutral_basis Point]
def nCol (A B C : Point) : Prop :=
  A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
  ¬ self.BetS A B C ∧ ¬ self.BetS A C B ∧ ¬ self.BetS B A C
-- … Col, Cong_3, TS, Triangle, OnCirc, InCirc, OutCirc
end euclidean_neutral_basis

class euclidean_neutral extends euclidean_neutral_basis Point where
  axiom_circle_center_radius :
    ∀ A B C J P, CI J A B C → euclidean_neutral_basis.OnCirc P J → Cong A P B C
  axiom_lower_dim : euclidean_neutral_basis.nCol PA PB PC
  …
```

**Why this and not the in-class default-valued-field form.** Earlier
versions of this file tried to put the derived defs *inside* the class
as default-valued fields (`name (args) : T := body`). The form
typechecks, but Julien's review flagged a soundness concern and the
proof-side then hit a blocker. Both push the same way:

- *Soundness (Julien)*: a default-valued field is overridable by an
  instance. If `Col` can be replaced, the cross-system equivalence
  theorems (Tarski ≡ Euclid ≡ Hilbert) — which are proved against the
  canonical `Col` — silently stop applying to those instances. With a
  namespaced `def`, the body is fixed.
- *Proofs*: a default-valued field is opaque from outside the class.
  `InCirc B J` cannot be constructed with the anonymous constructor
  because Lean doesn't see the field projection as definitionally
  equal to its body. `unfold`, `@[reducible]`, and `show` were all
  tested; none unfold a field projection. With a namespaced `def`,
  `show ∃ …` reduces the body and the constructor works.

Cost: a few deep-`extends` call sites in
`euclidean_neutral_ruler_compass` need `@euclidean_neutral_basis.OnCirc Point _ …`
to force typeclass synthesis through two `extends` levels (see
[lean_lsp_errors.md](lean_lsp_errors.md) §2).

| Rocq class | Lean class | Notes |
|---|---|---|
| (implicit) | `euclidean_neutral_basis` | Structural primitives only |
| `euclidean_neutral` | same | 17 axioms; references `nCol` and `OnCirc` from the basis namespace |
| `euclidean_neutral_ruler_compass` | same | 2 continuity postulates; needs `@`-applied `OnCirc`/`InCirc`/`OutCirc` |
| `euclidean_euclidean` | same | Euclid 5; references `nCol` |
| `area` | same | adds `EF`, `ET` + 18 area axioms; uses `Cong_3`, `TS`, `Triangle` |

### 3.4 `theories/Axioms/hilbert_axioms.v` → [Hilbert/Axioms.lean](../lean/geocoq_translate/GeocoqTranslate/Hilbert/Axioms.lean)

Hilbert's classical axiom system: six classes, three primitive sorts
(`Point`, `Line`, `Plane`) with their own equivalence relations and
incidence predicates, plus betweenness and congruence (both segment and
angle).

Same two-class-split pattern as Euclidean (§3.3). Seven derived
predicates of `Hilbert_neutral_dimensionless` live in the
`Hilbert_neutral_basis` namespace as plain `def`s:

| Derived def | What it says |
|---|---|
| `ColH A B C` | the three points lie on some line |
| `IncidLP l p` | every point of `l` is in plane `p` |
| `cut l A B` | `A`, `B` on opposite sides of line `l` |
| `outH P A B` | `A` is "out from `P` through `B`" |
| `disjoint A B C D` | segments `AB` and `CD` share no interior point |
| `same_side A B l` | `A`, `B` on the same side of `l` |
| `same_side' A B X Y` | extension that quantifies over all lines through `X`, `Y` |

Hilbert also has `Para` (parallel lines), which lives in its own
`Hilbert_euclidean` namespace as a separate `def` since it depends on
`Line` and `IncidLP`.

This translation needs the `@`-fix at *one* level of `extends` already
(not two as in Euclidean): `IncidLP l p` and `cut l A B` each take two
dependent-typed arguments from `Hilbert_neutral_basis`. The 1-deep
call sites in `pasch` and `line_on_plane` use
`@Hilbert_neutral_basis.IncidLP Point _ l p` etc.

| Lean class | Adds |
|---|---|
| `Hilbert_neutral_basis` | 12 primitives — structural only |
| `Hilbert_neutral_dimensionless` | 27 axioms across Groups I (Incidence), II (Order), III (Congruence); references derived defs via `Hilbert_neutral_basis.…` |
| `Hilbert_neutral_2D` | 2D variant of Pasch |
| `Hilbert_neutral_3D` | plane intersection + lower-dim-3 with `HS1..4` |
| `Hilbert_euclidean` | parallels uniqueness; uses `@Hilbert_euclidean.Para Point _` at call sites |
| `Hilbert_euclidean_ID` | adds decidability of line intersection |

### 3.5 `theories/Axioms/Definitions.v` → [Tarski/Definitions.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski/Definitions.lean) (partial)

Only the subset Ch02 needs so far: `OFSC` (Outer Five Segment Config,
Def 2.10) and `Cong_3` (triangle congruence, Def 4.4). Other definitions
from the Rocq file (`Bet_4`, `IFSC`, `Cong_4`, `Cong_5`, `Projp`, ...)
will be added here as later chapters reach them.

Lives in `namespace GeocoqTranslate.Tarski`, parameterised over
`[Tarski_neutral_dimensionless Tpoint]`. Both defs are plain `def` —
they only return Prop and take Point arguments, no dependent types
involved, so no `@`-fix needed at call sites.

### 3.6 `theories/Main/Tarski_dev/Ch02_cong.v` → [Tarski_dev/Ch02_cong.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Ch02_cong.lean)

**The first proof translation.** All 30 lemmas in 4 sections.
Schwabhäuser §1.1: congruence is an equivalence; symbol permutations;
five-segment-with-def; segment-construction uniqueness.

| Section | Lemmas | Uses |
|---|---|---|
| T1_1 (11) | `cong_reflexivity`, `cong_symmetry`, `cong_transitivity`, `cong_left_commutativity`, `cong_right_commutativity`, `cong_3421/4312/4321`, `cong_trivial_identity`, `cong_reverse_identity`, `cong_commutativity` | only `Tarski_neutral_dimensionless` |
| T1_2 (7) | `not_cong_2134`, `not_cong_1243/2143/3412/4312/3421/4321` | contrapositives of T1_1 |
| T1_3 (9) | `five_segment_with_def`, `cong_diff{,_2,_3,_4}`, `cong_3_sym`, `cong_3_swap{,_2}`, `cong3_transitivity` | uses `OFSC`, `Cong_3` from Definitions |
| T1_4 (7) | `eq_dec_points`, `distinct`, `l2_11`, `bet_cong3`, `construction_uniqueness`, `Cong_cases`, `Cong_perm` | needs `point_equality_decidability` |

**Translation style:** term-mode by default for the
permutation-chasing lemmas; `by`-block with `obtain` / `rcases` /
`subst` where Coq does destructuring or case splits. Sections expressed
as Lean `section ... end` blocks with their own `variable` declarations,
so T1_1–T1_3 sit under the neutral class and T1_4 under the
`_with_decidable_point_equality` extension.

**29 of 30 lemmas compiled first-try.** The one repair: `bet_cong3`
used `segment_construction A' B' B C`, which returns `Cong B' x B C`.
The next call (`l2_11`) needs `Cong B C B' x`. Coq's `Cong` hint tactic
silently inserted a `cong_symmetry`; Lean does not. Fix: bind the
symmetry explicitly:

```lean
have hBCBx : Cong B C B' x := cong_symmetry B' x B C hCong
exact ⟨x, h2, l2_11 A B C A' B' x h1 hBet h2 hBCBx, hBCBx⟩
```

This is the canonical example of what to expect when later chapters
lean more heavily on Coq's `auto with cong` automation — the explicit
permutation has to be supplied.

### 3.7 `theories/Elements/OriginalProofs/proposition_01.v` → [Elements/OriginalProofs/proposition_01.lean](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/proposition_01.lean)

**The first proposition from Euclid's *Elements*** — on a given segment
AB, construct an equilateral triangle. Recommended by Julien as the
first proof-translation test.

Statement:

```lean
theorem proposition_01 (A B : Point) (hAB : A ≠ B) :
    ∃ C, equilateral A B C ∧ Triangle A B C
```

The proof translates one-to-one with the Coq tactic script, organised
into three commented phases that mirror Euclid's conceptual structure:

1. **Build C as the circle/circle intersection.** Two circles via
   `postulate_Euclid3` (one at A through B, one at B through A); the
   extension point D from `lemma_localextension` provides the "outside"
   witness; the five derived-circle predicates (`InCirc B K`,
   `OutCirc D K`, `OnCirc B J`, `OnCirc D J`) are built with the
   `show ∃ … ; exact ⟨…⟩` pattern; `postulate_circle_circle` yields C.
2. **Derive `equilateral A B C`.** Six `Cong` rewrites chain
   `axiom_circle_center_radius` (twice — once per circle) with
   `lemma_congruencesymmetric`, `lemma_congruencetransitive`,
   `lemma_congruenceflip`, and `cn_equalityreverse` to produce
   `Cong A B B C` and `Cong B C C A`. `equilateral` is then constructed
   by anonymous-constructor + `show`.
3. **Show non-degeneracy (`Triangle A B C`).** Distinctness of the three
   sides from `axiom_nocollapse`, and three `¬ BetS` facts via
   `lemma_partnotequalwhole`. `Triangle` is then built by unfolding
   `Triangle` → `nCol` to its six-conjunct form.

**Dependencies, all already translated** (six prior Element lemma
files + the `equilateral` definition):
`lemma_inequalitysymmetric`, `lemma_localextension`,
`lemma_congruencesymmetric`, `lemma_congruencetransitive`,
`lemma_congruenceflip`, `lemma_partnotequalwhole`.

**Full verification.** Initially `lemma_partnotequalwhole` was
`sorry`-stubbed. The five-file dependency subtree was then translated:

| Lemma | Statement (informal) |
|---|---|
| `lemma_3_6a` | `BetS A B C → BetS A C D → BetS B C D` |
| `lemma_betweennotequal` | `BetS A B C → B ≠ C ∧ A ≠ B ∧ A ≠ C` |
| `lemma_extensionunique` | `BetS A B E ∧ BetS A B F ∧ Cong B E B F → E = F` |
| `lemma_3_7a` | `BetS A B C → BetS B C D → BetS A C D` |
| `lemma_3_7b` | `BetS A B C → BetS B C D → BetS A B D` |

With the stub replaced, **Proposition 1 has no `sorry` in transitive
closure** — fully verified end-to-end.

**Notable translation moves:**

- **`postulate_circle_circle` J/K swap.** Our `J` is the circle at A,
  our `K` is the circle at B. But the axiom is asymmetric: its `J` is
  the circle whose interior/exterior contains the test points, its `K`
  is the circle the test points sit on. We pass the Circle args as
  `K J` (not `J K`); Coq's `conclude` infers this implicitly, in Lean
  it's explicit. The conjuncts in the conclusion also come back in the
  swapped order — `OnCirc X K ∧ OnCirc X J`.
- **`¬ BetS` proofs are one-liners.** Each Coq block does three steps
  of `cn_equalityreverse` + `lemma_congruencetransitive` chasing
  because Coq's `Cong` hint database silently inserts those. In Lean
  we apply `lemma_partnotequalwhole` directly against the relevant
  `hCong_*` already in scope. Each `¬ BetS` is one line of `fun hBetS =>
  lemma_partnotequalwhole … hBetS hCong_…`.
- **`Col` short-circuited.** Coq has a separate `~ Col A B C` assertion
  before `Triangle A B C`. Our Lean version skips the intermediate
  `~ Col` step by proving `Triangle` (= `nCol` after unfolding)
  directly as a six-component `⟨…⟩`.

**LSP failures during translation:** none new. The `show ∃ …` pattern
for `def`-backed predicates was already established in
[lemma_localextension.lean](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/Lemmas/lemma_localextension.lean)
(see [lean_lsp_errors.md §12](lean_lsp_errors.md)).

## 4. Summary table

| Source | Items | Lean output | Status |
|---|---|---|---|
| [rocq_demo.v](../theories/Axioms/rocq_demo.v) | 5 theorems | [Scratch.lean](../lean/geocoq_translate/GeocoqTranslate/Scratch.lean) | Compiles. 4/5 first-try, 1 repaired (looping simp). |
| [tarski_axioms.v](../theories/Axioms/tarski_axioms.v) | 7 classes | [Tarski/Axioms.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski/Axioms.lean) | Compiles first-try. |
| [euclidean_axioms.v](../theories/Axioms/euclidean_axioms.v) | 4 classes + 8 derived defs | [Euclidean/Axioms.lean](../lean/geocoq_translate/GeocoqTranslate/Euclidean/Axioms.lean) | Two-class split: `euclidean_neutral_basis` (primitives) + namespaced `def`s + `euclidean_neutral` extending the basis. Mirrors Coq's `Definition` semantics. |
| [hilbert_axioms.v](../theories/Axioms/hilbert_axioms.v) | 6 classes + 7 derived defs + `Para` | [Hilbert/Axioms.lean](../lean/geocoq_translate/GeocoqTranslate/Hilbert/Axioms.lean) | Same two-class split as Euclidean. |
| [Definitions.v](../theories/Axioms/Definitions.v) (partial) | 2 defs | [Tarski/Definitions.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski/Definitions.lean) | First-try. More defs added as chapters need them. |
| [Tarski_dev/Ch02_cong.v](../theories/Main/Tarski_dev/Ch02_cong.v) | 30 lemmas | [Tarski_dev/Ch02_cong.lean](../lean/geocoq_translate/GeocoqTranslate/Tarski_dev/Ch02_cong.lean) | 29/30 first-try; 1 repair for an implicit `cong_symmetry` Coq's hint tactic was inserting. |
| [euclidean_defs.v](../theories/Elements/OriginalProofs/euclidean_defs.v) (partial) | 1 def | [euclidean_defs.lean](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/euclidean_defs.lean) | Only `equilateral` so far; more as later propositions need them. |
| [Elements/OriginalProofs/lemma_*.v](../theories/Elements/OriginalProofs/) (11 files) | 11 lemmas | [Elements/OriginalProofs/Lemmas/](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/Lemmas/) | All fully proved. Six "easy" (`lemma_inequalitysymmetric`, `lemma_localextension`, `lemma_congruence{symmetric,transitive,flip}`, `lemma_3_6a`); five "deep" (`lemma_betweennotequal`, `lemma_extensionunique`, `lemma_3_7a`, `lemma_3_7b`, `lemma_partnotequalwhole`). |
| [proposition_01.v](../theories/Elements/OriginalProofs/proposition_01.v) | 1 theorem | [proposition_01.lean](../lean/geocoq_translate/GeocoqTranslate/Elements/OriginalProofs/proposition_01.lean) | Statement + full proof; first-try compile. **No `sorry` in transitive closure** — fully verified. |

Library root [GeocoqTranslate.lean](../lean/geocoq_translate/GeocoqTranslate.lean)
imports all modules; `lake build` reports 22 jobs, 0 failures, 0 warnings.

## 5. What this branch now demonstrates

End-to-end, after Ch02 closed:

1. **Definitional translation works.** Three full axiom systems
   (Tarski, Euclidean, Hilbert) compile under `lake build`.
2. **Proof translation works for short proofs.** All 30 Ch02 lemmas
   translate one-to-one; 29 first-try, 1 with a tiny repair. Most are
   1–3-step `cong_*` chains where term-mode is shorter than Coq's
   tactic version.
3. **The hard part is going to be Coq's hint databases.** `Cong` and
   `eauto using ...` silently fill in permutation lemmas that Lean
   requires explicitly. So far, "make the implicit permutation
   explicit" has been the only mismatch.
4. **Coq's `Definition` translates to a namespaced `def`, not to an
   in-class default-valued field.** This was an explicit detour:
   Julien's review prompted a rewrite of Euclidean and Hilbert to the
   default-valued-field form, which initially looked syntactically
   closer to the Rocq source. Two independent issues forced reverting:
   Julien himself flagged that default-value fields are *overridable*
   (which would silently break the cross-system equivalence theorems),
   and the proof side then hit that they're also *opaque* outside the
   class (so values like `InCirc B J` can't be constructed). The
   namespaced-`def` form gives both correct semantics (fixed,
   unoverridable) and proof-side usability (`show ∃ …` unfolds the
   body, allowing the anonymous constructor). The cost — a few `@`-fix
   call sites at deep `extends` — is paid for it.

## 6. Open follow-ups

- **Other axiom files unfinished.** Sibling files in
  [theories/Axioms/](../theories/Axioms/) —
  `beeson_s_axioms.v`, `gupta_inspired_variant_axioms.v`,
  `makarios_variant_axioms.v`, `gelertner_inspired_axioms.v`,
  `continuity_axioms.v`, `parallel_postulates.v`,
  `adg_definitions.v` — are still Rocq-only. They follow the
  same `Class { ... }` pattern, so the same playbook should apply.
- **`Tarski/Definitions.lean` is a stub.** Only `OFSC` and `Cong_3`.
  Each new `Tarski_dev` chapter will pull in more defs (`Bet_4`,
  `IFSC`, `Col`, `OS`, `TS`, `Midpoint`, `Le`, `Lt`, ...). Worth
  doing as-needed rather than eagerly.
- **No model instance.** Nothing instantiates `Tarski_2D` on a concrete
  type like `ℝ × ℝ` yet. The Algebraic models in Rocq
  ([theories/Algebraic/](../theories/Algebraic/)) provide one — porting
  one of them would be the natural next milestone to prove the axioms
  aren't vacuous.
- **No cross-system equivalence yet.** Rocq's
  `Main/Meta_theory/Models` proves e.g. Tarski ↔ Hilbert. With both
  systems now in Lean, one such equivalence becomes portable.
- **Tactic substitution policy still ad-hoc.** Ch02 worked without
  needing `aesop`/`grind`/`linarith` — every step was an explicit
  lemma. Later chapters with `auto using ...` chains may force the
  decision: tag lemmas with `@[simp]`/`@[aesop]` attributes, or keep
  writing them out by hand.
