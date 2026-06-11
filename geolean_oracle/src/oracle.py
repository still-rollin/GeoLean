"""
End-to-end Coq proof oracle for GeoLean translation.

Given a .v file path and a lemma name, returns the list of resolved lemma
applications used in the proof — name + positional arguments after Coq's
unification, exactly as `Show Proof.` would print them.

Public API:
    extract_resolved_calls(coq_file: str, lemma_name: str) -> list[ResolvedCall]
"""

from __future__ import annotations

import os
import re
from dataclasses import dataclass

from .serapi import SerAPI, CoqError


# ---------------------------------------------------------------------------
# Data
# ---------------------------------------------------------------------------

@dataclass
class ResolvedCall:
    """One lemma/axiom application from the proof term, with resolved args."""
    name: str
    args: list[str]

    def as_signature(self) -> str:
        return f"{self.name} " + " ".join(self.args) if self.args else self.name


@dataclass
class OracleResult:
    lemma_name: str
    coq_source: str
    proof_term: str
    resolved_calls: list[ResolvedCall]


# ---------------------------------------------------------------------------
# 1. Coq source extraction
# ---------------------------------------------------------------------------

_LEMMA_PATTERN_TMPL = (
    r'((?:Lemma|Theorem|Corollary|Proposition|Remark|Fact)\s+{name}\b'
    r'.*?(?:Qed|Defined|Admitted)\s*\.)'
)

def extract_lemma_source(coq_path: str, lemma_name: str) -> str:
    with open(coq_path) as f:
        content = f.read()
    # Strip block comments to keep the regex simple.
    content = re.sub(r"\(\*.*?\*\)", "", content, flags=re.DOTALL)
    pat = _LEMMA_PATTERN_TMPL.format(name=re.escape(lemma_name))
    m = re.search(pat, content, re.DOTALL)
    if not m:
        raise ValueError(f"lemma {lemma_name!r} not found in {coq_path}")
    return m.group(1).strip()


def extract_requires(coq_path: str) -> list[str]:
    """Lines of `Require Export/Import ...` from the file header."""
    out: list[str] = []
    with open(coq_path) as f:
        for line in f:
            s = line.strip()
            if s.startswith("Require ") and s.endswith("."):
                out.append(s)
            elif s and not s.startswith("(*") and not s.startswith("Require"):
                # First non-Require line ends the header.
                break
    return out


# ---------------------------------------------------------------------------
# 2. Drive sertop and capture `Show Proof.` output
# ---------------------------------------------------------------------------

def _extract_section_header(coq_path: str) -> str:
    """
    Pull the `Section X. Context ...` declarations between Requires and
    the first Lemma. Returned as one string with newlines.
    """
    lines: list[str] = []
    with open(coq_path) as f:
        for raw in f:
            s = raw.strip()
            if not s or s.startswith("(*") or s.startswith("Require"):
                continue
            if s.startswith(("Lemma", "Theorem", "Corollary", "Proposition")):
                break
            lines.append(s)
            if s.startswith("Context"):
                break
    return "\n".join(lines)


def _strip_trailing_qed(lemma_src: str) -> tuple[str, str]:
    """
    Split lemma source into (body_without_qed, 'Qed.' | 'Defined.').
    Strips any `Show Proof.` sentences from the body so we own that emit.
    """
    m = re.search(
        r"(.*?)\b(Qed|Defined|Admitted)\s*\.\s*$",
        lemma_src,
        flags=re.DOTALL,
    )
    if not m:
        raise ValueError("no Qed/Defined/Admitted found in lemma source")
    body = m.group(1)
    body = re.sub(r"\bShow\s+Proof\s*\.\s*", "", body)
    return body.rstrip(), m.group(2) + "."


def run_proof(coq_path: str, lemma_name: str, q_paths: list[tuple[str, str]]) -> str:
    """
    Execute the file's preamble + the named lemma's body + `Show Proof.`
    through sertop. Returns the proof term as the printed text.

    We let sertop do the sentence splitting: one big Add per chunk.
    """
    requires = extract_requires(coq_path)
    section_header = _extract_section_header(coq_path)
    lemma_src = extract_lemma_source(coq_path, lemma_name)
    body, closer = _strip_trailing_qed(lemma_src)

    chunks: list[str] = [
        # Each Require is its own Add — fastest to fail-locate.
        *requires,
        section_header,
        body,             # statement + Proof. + tactics ... + close.
        "Show Proof.",
        closer,
        "End Euclid.",
    ]

    proof_text_parts: list[str] = []
    with SerAPI(q_paths=q_paths) as s:
        for chunk in chunks:
            chunk = chunk.strip()
            if not chunk:
                continue
            try:
                span_ids, _ = s.add(chunk)
            except CoqError as e:
                raise CoqError(f"Add failed on:\n  {chunk[:200]!r}\n  {e}") from None
            for sid in span_ids:
                try:
                    responses = s.exec(sid)
                except CoqError as e:
                    raise CoqError(f"Exec failed on span {sid}:\n  {chunk[:200]!r}\n  {e}") from None
                for r in responses:
                    if r.kind == "feedback" and r.message and not r.error:
                        proof_text_parts.append(r.message)
    full = "\n".join(proof_text_parts).strip()
    if not full:
        raise RuntimeError("no Show Proof output captured")
    return full


# ---------------------------------------------------------------------------
# 3. Split a lemma's source so we can insert `Show Proof.` before Qed
# ---------------------------------------------------------------------------

@dataclass
class _ProofSplit:
    before_qed: list[str]    # individual sentences up to (but not including) Qed
    qed_word: str            # "Qed" or "Defined"


_SENTENCE_RE = re.compile(
    r"""
    (?:
      [^."'(]                 # plain char that isn't . " ' (
      | "(?:[^"\\]|\\.)*"     # double-quoted string
      | '(?:[^'\\]|\\.)*'     # single-quoted string
      | \([^)]*\)             # bracketed group (rough)
    )+
    \.\s+                     # sentence-ending period followed by whitespace
    """,
    re.VERBOSE | re.DOTALL,
)


def _split_sentences(src: str) -> list[str]:
    """Greedily split a Coq source string into sentences ending in `. `."""
    pos = 0
    sentences = []
    while pos < len(src):
        m = _SENTENCE_RE.match(src, pos)
        if not m:
            # Last sentence may not have trailing whitespace
            tail = src[pos:].strip()
            if tail:
                sentences.append(tail)
            break
        sentences.append(m.group(0).strip())
        pos = m.end()
    return sentences


def _split_proof_for_show(lemma_src: str) -> _ProofSplit:
    sentences = _split_sentences(lemma_src + " ")  # trailing space helps matcher
    # Find the closing Qed/Defined and drop it; we add our own.
    qed_word = "Qed"
    while sentences and sentences[-1].rstrip(".").strip() in ("Qed", "Defined"):
        qed_word = sentences[-1].rstrip(".").strip()
        sentences.pop()
    return _ProofSplit(before_qed=sentences, qed_word=qed_word)


# ---------------------------------------------------------------------------
# 4. Parse `Show Proof` term to extract resolved lemma applications
# ---------------------------------------------------------------------------

# A *call* in a Show Proof term looks like `name arg1 arg2 ... argN`
# inside an application context, OR appears in `let _ := name args in ...`.
# We walk the term token-by-token; whenever we hit a known lemma/axiom
# identifier, we collect the following atoms as its args.

_IDENT_PREFIXES = ("lemma_", "axiom_", "cn_", "proposition_")


def is_oracle_identifier(name: str) -> bool:
    return any(name.startswith(p) for p in _IDENT_PREFIXES)


_TOKEN_RE = re.compile(
    r"""
    "(?:[^"\\]|\\.)*"          # quoted string (rare)
    | [A-Za-z_][A-Za-z0-9_']*  # identifier
    | [()]                     # paren
    | [^\s()]+                 # anything else as a token (e.g., := ->)
    """,
    re.VERBOSE,
)


def _tokenize(s: str) -> list[str]:
    return _TOKEN_RE.findall(s)


# Keywords that terminate an application's argument list.
_STOP_TOKENS = {
    "in", ":", ":=", "=>", "->", "let", "fun", "match", "with", "end",
    "if", "then", "else", "fix", "cofix", "forall", "exists",
    "Qed", "Defined",
}


def parse_resolved_calls(proof_term: str) -> list[ResolvedCall]:
    """
    Walk the proof term token stream and extract resolved lemma applications.

    Coq's `Show Proof.` often emits an indirection:

        let e : <forall-type> := lemma_X in
        e arg1 arg2 ...

    when type inference needed to specialize the lemma. We detect this
    pattern and treat `e arg1 arg2 ...` as `lemma_X arg1 arg2 ...`.

    Direct applications `lemma_X arg1 arg2 ...` are also captured.

    Returns calls in source order, deduplicated only if completely identical
    on consecutive occurrences (Coq sometimes re-prints).
    """
    tokens = _tokenize(proof_term)
    calls: list[ResolvedCall] = []
    aliases: dict[str, str] = {}   # local-name → lemma_name
    i = 0
    while i < len(tokens):
        tok = tokens[i]
        # Pattern 1: `let NAME : ... := lemma_X in ...` — record alias.
        if tok == "let" and (j := _try_match_let_alias(tokens, i)) is not None:
            alias_name, lemma_name, after = j
            aliases[alias_name] = lemma_name
            i = after
            continue
        # Pattern 2: direct `lemma_X args`.
        if is_oracle_identifier(tok):
            args, j = _collect_args(tokens, i + 1)
            _append_unique(calls, ResolvedCall(name=tok, args=args))
            i = j
            continue
        # Pattern 3: aliased application `aliased_name args`.
        if tok in aliases:
            args, j = _collect_args(tokens, i + 1)
            # Skip if no args — that's just a use of the binding, not a call.
            if args:
                _append_unique(calls, ResolvedCall(name=aliases[tok], args=args))
            i = j
            continue
        i += 1
    return calls


def _append_unique(calls: list[ResolvedCall], call: ResolvedCall) -> None:
    """Skip back-to-back exact duplicates (Coq prints the term twice with
    `Show Proof.` followed by `Qed.` in some cases)."""
    if calls and calls[-1].name == call.name and calls[-1].args == call.args:
        return
    calls.append(call)


def _try_match_let_alias(
    tokens: list[str], i: int
) -> tuple[str, str, int] | None:
    """
    Try to match the pattern:
        let <NAME> [: ... ] := <lemma_X> in
    starting at tokens[i] == "let". Returns (NAME, lemma_X, index_after_'in')
    or None if it's not this pattern.

    We're lenient with the `: <type>` annotation, which may span many
    tokens including parens. The crucial markers are `:=` and `in`.
    """
    assert tokens[i] == "let"
    if i + 1 >= len(tokens):
        return None
    alias_name = tokens[i + 1]
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", alias_name):
        return None
    # Find `:=` at the top level (paren depth 0), scanning forward.
    depth = 0
    j = i + 2
    coloneq_at = None
    while j < len(tokens):
        t = tokens[j]
        if t == "(":
            depth += 1
        elif t == ")":
            depth -= 1
            if depth < 0:
                return None
        elif depth == 0 and t == ":=":
            coloneq_at = j
            break
        elif depth == 0 and t == "let":
            # Outer let must close before inner let starts at same depth.
            return None
        j += 1
    if coloneq_at is None:
        return None
    # The RHS should be an oracle identifier followed by `in` at depth 0.
    k = coloneq_at + 1
    if k >= len(tokens):
        return None
    rhs = tokens[k]
    if not is_oracle_identifier(rhs):
        return None
    if k + 1 >= len(tokens) or tokens[k + 1] != "in":
        return None
    return alias_name, rhs, k + 2


def _collect_args(tokens: list[str], start: int) -> tuple[list[str], int]:
    """
    From position `start`, collect argument atoms until we hit a stop
    token or run off the end. A parenthesised group counts as ONE arg
    (we record its source-flattened form).
    """
    args: list[str] = []
    i = start
    while i < len(tokens):
        tok = tokens[i]
        if tok in _STOP_TOKENS:
            break
        if tok == ")":
            # We've exited the enclosing application.
            break
        if tok == "(":
            grp, j = _collect_paren_group(tokens, i)
            args.append(grp)
            i = j
            continue
        # An ordinary atom — identifier, number, etc.
        # Stop if it's another oracle identifier — that's the start of a new call.
        if is_oracle_identifier(tok):
            break
        args.append(tok)
        i += 1
    return args, i


def _collect_paren_group(tokens: list[str], start: int) -> tuple[str, int]:
    """Collect a parenthesised group starting at tokens[start] == '('.
    Returns (group_text, index_after_group)."""
    assert tokens[start] == "("
    depth = 0
    parts: list[str] = []
    i = start
    while i < len(tokens):
        t = tokens[i]
        parts.append(t)
        if t == "(":
            depth += 1
        elif t == ")":
            depth -= 1
            if depth == 0:
                return " ".join(parts), i + 1
        i += 1
    return " ".join(parts), i


# ---------------------------------------------------------------------------
# 5. Top-level
# ---------------------------------------------------------------------------

def default_q_paths() -> list[tuple[str, str]]:
    """Where sertop should look for GeoCoq's compiled .vo files."""
    cwd = os.getcwd()
    return [(os.path.join(cwd, "_build/default/theories"), "GeoCoq")]


def extract_resolved_calls(
    coq_file: str,
    lemma_name: str,
    q_paths: list[tuple[str, str]] | None = None,
) -> OracleResult:
    """
    End-to-end: run `lemma_name` from `coq_file` through Coq, capture
    `Show Proof.` output, parse it for resolved lemma applications.
    """
    qp = q_paths or default_q_paths()
    coq_source = extract_lemma_source(coq_file, lemma_name)
    proof_term = run_proof(coq_file, lemma_name, qp)
    calls = parse_resolved_calls(proof_term)
    return OracleResult(
        lemma_name=lemma_name,
        coq_source=coq_source,
        proof_term=proof_term,
        resolved_calls=calls,
    )


# ---------------------------------------------------------------------------
# 6. Bulk extraction — one call per .v file
# ---------------------------------------------------------------------------

_LEMMA_NAME_RE = re.compile(
    r"^\s*(?:Lemma|Theorem|Corollary|Proposition|Remark|Fact)\s+(\w+)\b",
    re.MULTILINE,
)


def find_all_lemma_names(coq_file: str) -> list[str]:
    """All top-level Lemma/Theorem/Proposition/Corollary names in source order."""
    with open(coq_file) as f:
        content = f.read()
    content = re.sub(r"\(\*.*?\*\)", "", content, flags=re.DOTALL)
    return _LEMMA_NAME_RE.findall(content)


def extract_resolved_calls_for_file(
    coq_file: str,
    q_paths: list[tuple[str, str]] | None = None,
) -> dict:
    """
    Bulk-extract resolved calls for every Lemma/Theorem/Proposition in a
    single .v file. Returns a dict keyed by lemma name:

        {
          "lemma_name_1": [{"theorem": "lemma_X", "args": ["A","B","H"]}, ...],
          "lemma_name_2": {"error": "..."},
          ...
        }

    A lemma that fails (e.g., missing dependency, parse error) records
    `{"error": str}` instead of stopping the batch.
    """
    qp = q_paths or default_q_paths()
    result: dict = {}
    for name in find_all_lemma_names(coq_file):
        try:
            r = extract_resolved_calls(coq_file, name, q_paths=qp)
            result[name] = [
                {"theorem": c.name, "args": c.args} for c in r.resolved_calls
            ]
        except Exception as e:
            result[name] = {"error": str(e)}
    return result
