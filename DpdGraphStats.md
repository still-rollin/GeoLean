# Statistical Summary of the `dpdgraph` Runs

## Per-Subsystem Totals

| Subsystem | Modules | Symbols (nodes) | Dependencies (edges) | Wall Time |
|------------|----------|----------------|---------------------|-----------|
| axioms | 13 | 568 | 2,216 | <1s |
| tarski_dev | 19 | 1,298 | 15,823 | <1s |
| elements | 239 | 339* | 6,356 | <1s |
| ch02_cong (test) | 3 | 234 | 968 | <1s |

> **\*** Lower than expected because each Element file usually defines exactly one lemma.  
> `339 ≈ 239 lemmas + ~100 inherited axioms/definitions surfaced as nodes`.

---

## Edge Density (Complexity per File)

| Subsystem | Edges / Module |
|------------|---------------|
| tarski_dev | 833 |
| axioms | 170 |
| elements | 27 |

### Observation

`Tarski_dev` is by far the most interconnected subsystem. Each chapter pulls heavily from previous chapters, creating a dense dependency graph.

`Elements` lemmas are mostly leaves: each lemma typically depends on ~25 other symbols, but relatively few later results depend on it.

---

## In-Degree Distribution (Elements)

Percentage of all **6,356 Element dependency edges** accounted for by the most frequently used symbols.

| Top-K Symbols | Cumulative In-Weight | % of All Uses |
|--------------|----------------------|---------------|
| Top 1 (`Col`) | 95,418 | 27% |
| Top 5 | 309,316 | 87% |
| Top 10 | 369,116 | ~95% |
| Top 20 | 386,651 | ~98% |
| Remaining 319 symbols | ~8,000 | ~2% |

### Observation

Dependency usage is extremely concentrated.

The five symbols

- `Col`
- `Point`
- `BetS`
- `neq`
- `Cong`

account for **87% of all dependency weight**.

All five are axioms or primitive definitions and have already been translated.

---

## Already-Translated Coverage

Among the **30 most-depended-upon non-axiom Element lemmas**:

| Status | Count |
|----------|-------|
| ✓ Already translated | 5 |
| Not yet translated | 25 |

### Currently Translated

- `lemma_betweennotequal`
- `lemma_inequalitysymmetric`
- `lemma_congruenceflip`
- `lemma_congruencesymmetric`
- `lemma_congruencetransitive`

These five lemmas collectively account for:

> **1,713 dependent references**

### Highest-Impact Next Targets

Translating the next five most-used lemmas would add coverage of approximately:

> **2,575 additional references**

Target lemmas:

1. `lemma_collinearorder`
2. `lemma_collinear4`
3. `lemma_ray4`
4. `lemma_NCorder`
5. `lemma_parallelflip`

---

## Per-Axiom-System Size

Symbol counts extracted from `axioms.dpd`.

| Axiom System | Symbols |
|--------------|----------|
| Definitions (Tarski-derived) | 168 |
| adg_definitions | 89 |
| tarski_axioms | 39 |
| hilbert_axioms | 73 |
| euclidean_axioms | 64 |
| continuity_axioms | 39 |
| parallel_postulates | 31 |
| beeson_s_axioms | 22 |
| gupta_inspired_variant_axioms | 24 |
| makarios_variant_axioms | 18 |
| rocq_demo + playground | 11 |

### Observation

If the following are excluded:

- Beeson variant axioms
- Gupta-inspired variant axioms
- Makarios variant axioms
- Parallel-postulate variants

then approximately:

> **95 symbols (~17% of the axiom layer)**

can be removed from consideration without affecting the primary translation pipeline.

---

## Build-Status Gap

| Directory | Source `.v` Files | Built `.vo` Files | Skipped |
|------------|------------------|------------------|----------|
| Axioms/ | 14 | 13 | 1 (`gelertner_inspired_axioms`) |
| Tarski_dev/ | 27 | 19 | 8 |
| Elements/OriginalProofs/ | 238 | 238 | 0 |

### Observation

When estimating the translation workload, the relevant count is:

> **270 buildable files**, not 463 source files.

The remaining **193 files** are primarily located in:

- `Algebraic/`
- `Coinc/`
- `Main/Highschool/`
- `Main/Annexes/`
- `Main/Meta_theory/`

These subsystems are not currently part of the active Dune build pipeline.

---

# Headline Numbers

| Metric | Value |
|----------|--------|
| Total source files | 463 |
| Buildable / depgraphable files | 270 |
| Total symbols across analyzed subgraphs | 2,205 |
| Total dependency edges | 24,395 |
| Dependency weight concentrated in top 5 axiom symbols | 87% |
| Top-30 non-axiom lemmas already translated | 5 |
| References covered by translated top lemmas | 1,713 |
| Additional references covered by next 5 target lemmas | ~2,575 |
| Axiom-layer code removable via variant-axiom pruning | ~17% |

---

# Key Takeaways

1. **The dependency graph is highly concentrated.**
   - Five foundational symbols account for **87%** of all Element dependency weight.

2. **Translation progress is already hitting high-impact lemmas.**
   - The current Prop. 1 translation chain covers **1,713 downstream references**.

3. **The next translation targets offer excellent leverage.**
   - Translating five additional lemmas would add roughly **2,575 dependent references**.

4. **`tarski_dev` is the primary complexity bottleneck.**
   - It contains over **64%** of all observed dependency edges.

5. **The practical translation scope is much smaller than the repository size suggests.**
   - Only **270 of 463 files** are currently buildable and dependency-analyzable.

6. **Variant axiom systems can be safely deferred.**
   - Eliminating them reduces the axiom layer by roughly **17%** without affecting the main translation path.
