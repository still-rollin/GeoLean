#!/usr/bin/env python3
"""
coq_to_lean_brief.py

MCP tool (or standalone CLI) that, given a Coq .v file + lemma name +
Lean project root, returns everything needed for a one-shot translation:

  - coq_source      : the lemma statement + proof verbatim
  - signatures      : one signature line per already-ported dependency
  - missing         : dep names not yet found in the Lean project
  - suggested_imports: import lines needed for the found deps

Usage (CLI):
  python coq_to_lean_brief.py \
      --coq path/to/GeoCoq/Elements/Book_1/proposition_02.v \
      --lemma proposition_02 \
      --lean path/to/GeoLean

Usage (MCP):
  Register with `claude mcp add` — see bottom of file.
"""

import re
import os
import glob
import json
import argparse
import sys
from pathlib import Path
from typing import Optional


# ---------------------------------------------------------------------------
# 1. COQ SOURCE EXTRACTION
# ---------------------------------------------------------------------------

def extract_coq_lemma(coq_path: str, lemma_name: str) -> Optional[str]:
    """
    Extract the full text of a named lemma/theorem/definition from a .v file.
    Returns everything from the opening keyword line through the closing Qed/Defined/Admitted.
    """
    with open(coq_path) as f:
        content = f.read()

    # Strip block comments (non-nested approximation; good enough for Elements)
    content_stripped = re.sub(r'\(\*.*?\*\)', '', content, flags=re.DOTALL)

    # Match the lemma header
    pattern = rf'((?:Lemma|Theorem|Definition|Corollary|Proposition|Remark|Fact)\s+{re.escape(lemma_name)}\b.*?(?:Qed|Defined|Admitted)\s*\.)'
    m = re.search(pattern, content_stripped, re.DOTALL)
    if m:
        return m.group(1).strip()

    # Fallback: return from lemma keyword to end of file section
    pattern2 = rf'((?:Lemma|Theorem|Definition|Corollary|Proposition)\s+{re.escape(lemma_name)}\b[^\n]*(?:\n(?!(?:Lemma|Theorem|Definition|Corollary|Proposition)\s).*)*)'
    m2 = re.search(pattern2, content_stripped, re.DOTALL)
    if m2:
        return m2.group(1).strip()

    return None


# ---------------------------------------------------------------------------
# 2. DEPENDENCY EXTRACTION FROM COQ PROOF
# ---------------------------------------------------------------------------

# Patterns covering the Elements proof style:
#   conclude X / forward_using X / conclude_def X
#   apply X / exact X / rewrite X / rewrite <- X
#   use X (some local conventions)
DEP_PATTERNS = [
    r'conclude\s+(\w+)',
    r'conclude_def\s+(\w+)',
    r'forward_using\s+(\w+)',
    r'apply\s+\(?(\w+)',
    r'exact\s+\(?(\w+)',
    r'rewrite\s+<?-?\s*\(?(\w+)',
    r'use\s+(\w+)',
    r'eauto\s+using\s+([\w,\s]+)',   # may capture multiple
]

# Names to always ignore — Coq builtins / tactics / common keywords
IGNORE = {
    'auto', 'eauto', 'tauto', 'intuition', 'simpl', 'ring', 'linarith',
    'omega', 'lia', 'trivial', 'assumption', 'reflexivity', 'symmetry',
    'transitivity', 'split', 'left', 'right', 'exists', 'constructor',
    'induction', 'destruct', 'inversion', 'subst', 'contradiction',
    'exfalso', 'absurd', 'unfold', 'fold', 'change', 'pose', 'have',
    'assert', 'specialize', 'generalize', 'revert', 'clear', 'rename',
    'intro', 'intros', 'move', 'case', 'elim', 'field', 'norm_num',
    'simp', 'decide', 'rfl', 'exact', 'apply', 'rewrite', 'use',
    'conclude', 'forward_using', 'conclude_def',
    'True', 'False', 'Prop', 'Type', 'Set',
    'eq', 'and', 'or', 'not', 'iff',
    # GeoCoq definition names used with conclude_def (not lemmas)
    'Col', 'Cong', 'Bet', 'Per', 'Perp', 'Midpoint', 'BetS',
    'Le', 'Lt', 'Ge', 'Gt', 'Out', 'TS', 'OS', 'Coplanar',
    'ReflectL', 'Reflect', 'Triangle', 'nCol',
}

def extract_deps(coq_source: str) -> list[str]:
    """
    Extract dependency lemma names from a Coq proof source string.
    Returns a deduplicated list preserving first-occurrence order.
    """
    names = []
    seen = set()

    for pat in DEP_PATTERNS:
        for m in re.finditer(pat, coq_source):
            # eauto using may give "L1, L2" — split on comma/space
            raw = m.group(1)
            candidates = re.split(r'[\s,]+', raw)
            for name in candidates:
                name = name.strip()
                if name and name not in IGNORE and not name[0].isdigit():
                    # skip single letters (A B C point vars) and hypothesis names (H, HAB, h1…)
                    if re.fullmatch(r'[A-Za-z]|[Hh]\w*', name):
                        continue
                    if name not in seen:
                        seen.add(name)
                        names.append(name)

    return names


# ---------------------------------------------------------------------------
# 3. LEAN SIGNATURE CACHE
# ---------------------------------------------------------------------------

# Top-level declaration start (theorem/lemma/def/abbrev/axiom/instance).
# Captures the kind and name; we then walk forward line-by-line to capture
# the full multi-line signature.
DECL_START = re.compile(
    r'^(\s*)(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+)?'
    r'(theorem|lemma|def|abbrev|axiom|instance)\s+(\w+)\b'
)

# Class header may span multiple lines. Match the `class NAME` line; the
# `where` may appear on a later line (with `extends ... where`). We use a
# follow-up scan to confirm the `where` and find the body.
CLASS_HEADER = re.compile(r'^(\s*)class\s+(\w+)\b')
# A line ending in `where` (possibly with trailing whitespace) marks the
# end of a class header — body starts immediately after.
WHERE_END = re.compile(r'\bwhere\s*$')

# Inside a class block, a field is an indented `name :` line.
CLASS_FIELD = re.compile(r'^(\s+)(\w+)\s*:')

# Strip everything from `:= ` onward (proof body).
_PROOF_BODY = re.compile(r'\s*:=.*$', re.DOTALL)

def _capture_signature(lines: list[str], start_idx: int, base_indent: int) -> tuple[str, int]:
    """
    Starting at lines[start_idx] (which begins a declaration), accumulate the
    signature spanning multiple lines until we hit:
      - a `:= ` (proof body starts), OR
      - a blank line, OR
      - a line at base_indent or less that itself starts a new declaration.
    Returns (signature_str, lines_consumed).
    """
    pieces = []
    i = start_idx
    while i < len(lines):
        line = lines[i]
        # Stop on blank line (signature done)
        if i > start_idx and not line.strip():
            break
        # Stop if new decl at same or smaller indent (after first line)
        if i > start_idx:
            stripped = line.lstrip()
            cur_indent = len(line) - len(stripped)
            if cur_indent <= base_indent and (
                DECL_START.match(line) or CLASS_HEADER.match(line)
                or stripped.startswith('end ') or stripped.startswith('namespace ')
            ):
                break
        pieces.append(line.rstrip())
        # If this line contains `:= `, signature ends here
        if ':=' in line:
            # Truncate this final piece before `:=`
            pieces[-1] = pieces[-1].split(':=')[0].rstrip()
            i += 1
            break
        i += 1
    sig = ' '.join(p.strip() for p in pieces if p.strip())
    sig = _PROOF_BODY.sub('', sig).strip()
    return sig, i - start_idx + 1

def _split_kind_name_rest(sig: str) -> tuple[str, str, str]:
    """Given a top-level signature string, return (kind, name, rest_after_name)."""
    m = re.match(
        r'^\s*(?:@\[[^\]]*\]\s*)?'
        r'(?:private\s+|protected\s+|noncomputable\s+)?'
        r'(theorem|lemma|def|abbrev|axiom|instance)\s+(\w+)\b(.*)$',
        sig, re.DOTALL
    )
    if not m:
        return ('', '', sig)
    return (m.group(1), m.group(2), m.group(3).strip())

def build_signature_cache(lean_root: str) -> dict[str, dict]:
    """
    Walk all .lean files under lean_root and extract:
      - top-level declarations (theorem / lemma / def / abbrev / axiom / instance)
      - class field declarations (the project's axioms live here)
    Captures multi-line signatures correctly.
    """
    cache = {}
    lean_root = os.path.expanduser(lean_root)

    # If the lean_root directory's basename starts with an uppercase letter
    # (Lean convention for a package source root, e.g. `GeocoqTranslate/`),
    # use it as the namespace prefix in import paths.
    root_basename = os.path.basename(os.path.normpath(lean_root))
    use_root_ns = bool(root_basename) and root_basename[0].isupper()

    for lean_file in glob.glob(f"{lean_root}/**/*.lean", recursive=True):
        rel = os.path.relpath(lean_file, lean_root)
        rel_dotted = rel.replace(os.sep, '.').removesuffix('.lean')
        import_path = f"{root_basename}.{rel_dotted}" if use_root_ns else rel_dotted

        try:
            with open(lean_file, encoding='utf-8', errors='ignore') as f:
                lines = f.read().splitlines()
        except OSError:
            continue

        i = 0
        in_class_block = False
        class_indent = -1
        class_name = ''
        while i < len(lines):
            line = lines[i]
            stripped = line.lstrip()
            cur_indent = len(line) - len(stripped)

            # End of class block?
            if in_class_block and stripped and cur_indent <= class_indent:
                in_class_block = False

            # Detect class block start. The `where` keyword that opens the
            # body may be on the same line as `class NAME`, or on a later
            # line (after `extends ...`). Advance past the header until we
            # see a line ending in `where`.
            m_class = CLASS_HEADER.match(line)
            if m_class:
                class_indent = len(m_class.group(1))
                class_name = m_class.group(2)
                # Walk to the `where` line.
                j = i
                found_where = False
                while j < len(lines):
                    if WHERE_END.search(lines[j]):
                        found_where = True
                        break
                    # Bail if we hit a blank line followed by something
                    # that isn't part of the header — keeps the scan tight.
                    j += 1
                    if j - i > 10:
                        break
                if found_where:
                    in_class_block = True
                    i = j + 1
                    continue
                # No `where` found — not a class block (likely `class abbrev`).
                i += 1
                continue

            # Class field inside a class block
            if in_class_block:
                m_field = CLASS_FIELD.match(line)
                if m_field and len(m_field.group(1)) > class_indent:
                    # Skip if it's actually a class with `extends ... where` followup
                    field_name = m_field.group(2)
                    # Capture field signature: from this line until next field at same indent
                    field_indent = len(m_field.group(1))
                    sig_pieces = [line.rstrip()]
                    j = i + 1
                    while j < len(lines):
                        nxt = lines[j]
                        nxt_strip = nxt.lstrip()
                        if not nxt_strip:
                            j += 1
                            continue
                        nxt_indent = len(nxt) - len(nxt_strip)
                        # Stop on same-indent field, or smaller-indent end
                        if nxt_indent <= field_indent:
                            break
                        sig_pieces.append(nxt.rstrip())
                        j += 1
                    sig_text = ' '.join(p.strip() for p in sig_pieces)
                    # Split off "name :" prefix to get the type
                    type_m = re.match(rf'^{re.escape(field_name)}\s*:\s*(.*)$', sig_text.strip())
                    type_str = type_m.group(1).strip() if type_m else sig_text
                    sig_line = f"axiom {field_name} : {type_str}   -- field of {class_name}"
                    if not re.fullmatch(r'[A-Z]|H[A-Z]\w*', field_name):
                        cache[field_name] = {
                            "kind": "class_field",
                            "params": "",
                            "conclusion": type_str,
                            "signature": sig_line,
                            "file": lean_file,
                            "import": import_path,
                        }
                    i = j
                    continue
                i += 1
                continue

            # Top-level declaration
            m_decl = DECL_START.match(line)
            if m_decl:
                base_indent = len(m_decl.group(1))
                sig, consumed = _capture_signature(lines, i, base_indent)
                kind, name, _rest = _split_kind_name_rest(sig)
                # Skip hypothesis-shaped names (single uppercase, H-prefix)
                if name and not re.fullmatch(r'[A-Z]|H[A-Z]\w*', name):
                    cache[name] = {
                        "kind": kind,
                        "params": "",
                        "conclusion": sig,
                        "signature": sig,
                        "file": lean_file,
                        "import": import_path,
                    }
                i += consumed
                continue

            i += 1

    return cache


# ---------------------------------------------------------------------------
# 4. IMPORT INFERENCE
# ---------------------------------------------------------------------------

def infer_imports(dep_names: list[str], cache: dict) -> list[str]:
    """
    For each found dependency, return the import line needed.
    Deduplicated, sorted.
    """
    imports = set()
    for name in dep_names:
        if name in cache:
            imports.add(f"import {cache[name]['import']}")
    return sorted(imports)


# ---------------------------------------------------------------------------
# 5. MAIN TOOL FUNCTION
# ---------------------------------------------------------------------------

def coq_to_lean_brief(
    coq_path: str,
    lemma_name: str,
    lean_project_root: str,
) -> dict:
    """
    Main entry point — returns the context dict for one-shot translation.
    """
    # 1. Extract Coq source
    coq_source = extract_coq_lemma(coq_path, lemma_name)
    if coq_source is None:
        return {
            "error": f"Lemma '{lemma_name}' not found in {coq_path}",
            "coq_source": None,
            "signatures": [],
            "missing": [],
            "suggested_imports": [],
        }

    # 2. Extract dependencies
    deps = extract_deps(coq_source)

    # 3. Build signature cache
    cache = build_signature_cache(lean_project_root)

    # 4. Look up each dep
    signatures = []
    missing = []
    for dep in deps:
        if dep in cache:
            signatures.append(cache[dep]["signature"])
        else:
            missing.append(dep)

    # 5. Infer imports
    found_deps = [d for d in deps if d in cache]
    suggested_imports = infer_imports(found_deps, cache)

    return {
        "coq_source": coq_source,
        "signatures": signatures,
        "missing": missing,
        "suggested_imports": suggested_imports,
    }


# ---------------------------------------------------------------------------
# 6. PRETTY PRINT (for CLI / Claude context injection)
# ---------------------------------------------------------------------------

def format_for_context(result: dict) -> str:
    """
    Format the result as a clean block ready to paste into a Claude prompt.
    """
    if result.get("error"):
        return f"ERROR: {result['error']}"

    lines = []

    lines.append("=== COQ SOURCE ===")
    lines.append(result["coq_source"])
    lines.append("")

    if result["signatures"]:
        lines.append("=== LEAN SIGNATURES OF DEPENDENCIES ===")
        for sig in result["signatures"]:
            lines.append(sig)
        lines.append("")

    if result["missing"]:
        lines.append("=== MISSING (not yet ported — use sorry or translate first) ===")
        for m in result["missing"]:
            lines.append(f"  {m}")
        lines.append("")

    if result["suggested_imports"]:
        lines.append("=== SUGGESTED IMPORTS ===")
        for imp in result["suggested_imports"]:
            lines.append(imp)
        lines.append("")

    return "\n".join(lines)


# ---------------------------------------------------------------------------
# 7. CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Extract Coq lemma + Lean dependency signatures for one-shot translation"
    )
    parser.add_argument("--coq", required=True, help="Path to .v file")
    parser.add_argument("--lemma", required=True, help="Lemma name to extract")
    parser.add_argument("--lean", required=True, help="GeoLean project root")
    parser.add_argument("--json", action="store_true", help="Output raw JSON instead of formatted text")
    args = parser.parse_args()

    result = coq_to_lean_brief(args.coq, args.lemma, args.lean)

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(format_for_context(result))


# ---------------------------------------------------------------------------
# 8. MCP SERVER (fastmcp)
# ---------------------------------------------------------------------------

def serve_mcp():
    """
    Expose coq_to_lean_brief as an MCP tool via fastmcp (stdio transport).
    Register with:
        claude mcp add coq-brief -- python /path/to/coq_to_lean_brief.py --mcp
    """
    try:
        from mcp.server.fastmcp import FastMCP
    except ImportError:
        print("fastmcp not installed. Run: pip install fastmcp", file=sys.stderr)
        sys.exit(1)

    mcp = FastMCP("coq-lean-brief")

    @mcp.tool()
    def coq_to_lean_brief_tool(
        coq_path: str,
        lemma_name: str,
        lean_project_root: str,
    ) -> dict:
        """
        Given a Coq .v file path, a lemma name, and the GeoLean project root,
        returns:
          - coq_source: the lemma + proof verbatim
          - signatures: one-line Lean signatures for each dependency found in the project
          - missing: dependency names not yet ported to Lean
          - suggested_imports: import statements needed for found deps

        Use this before translating a Coq lemma to get all context in one call.
        """
        return coq_to_lean_brief(coq_path, lemma_name, lean_project_root)

    mcp.run()


if __name__ == "__main__":
    if "--mcp" in sys.argv:
        sys.argv.remove("--mcp")
        serve_mcp()
    else:
        main()