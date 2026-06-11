"""
MCP server for the geolean translation oracle.

Exposes two tools to Claude Code:
  * get_resolved_calls(coq_file, lemma_name) — targeted lookup for a single lemma
  * get_resolved_calls_for_file(coq_file)    — bulk extract for a whole .v file

Both return Coq's resolved lemma applications: name + positional args, after
unification, exactly as `Show Proof.` would print them.

Run standalone:
    python3 -m src.server          (from geolean_oracle/)

Or register with Claude Code via .mcp.json:
    {
      "mcpServers": {
        "geolean-oracle": {
          "command": "python3",
          "args": ["-m", "src.server"],
          "cwd": "/path/to/GeoCoq/geolean_oracle"
        }
      }
    }
"""

from __future__ import annotations

import os
import sys

# Make `from .oracle import ...` work both as `python3 -m src.server`
# and `python3 src/server.py` invocations.
if __package__ in (None, ""):
    _this = os.path.dirname(os.path.abspath(__file__))
    sys.path.insert(0, os.path.dirname(_this))
    from src.oracle import (                           # type: ignore
        extract_resolved_calls,
        extract_resolved_calls_for_file,
    )
else:
    from .oracle import (
        extract_resolved_calls,
        extract_resolved_calls_for_file,
    )


def _build_server():
    try:
        from mcp.server.fastmcp import FastMCP
    except ImportError:
        print(
            "fastmcp not installed. Run: pip install 'mcp[cli]' fastmcp",
            file=sys.stderr,
        )
        sys.exit(1)

    mcp = FastMCP("geolean-oracle")

    @mcp.tool()
    def get_resolved_calls(coq_file: str, lemma_name: str) -> dict:
        """
        Return Coq's resolved lemma applications with positional args
        for ONE lemma. Use during translation when you need the exact
        argument order Coq used.

        Args:
          coq_file:   path to a .v file under theories/ (relative or absolute)
          lemma_name: the Lemma/Theorem name to extract

        Returns:
          {
            "coq_source": "<the verbatim Lemma … Qed text>",
            "resolved_calls": [
              {"theorem": "lemma_X", "args": ["A", "B", "H"]},
              ...
            ]
          }
        """
        coq_file = _resolve(coq_file)
        r = extract_resolved_calls(coq_file, lemma_name)
        return {
            "coq_source": r.coq_source,
            "resolved_calls": [
                {"theorem": c.name, "args": c.args} for c in r.resolved_calls
            ],
        }

    @mcp.tool()
    def get_resolved_calls_for_file(coq_file: str) -> dict:
        """
        Return resolved calls for EVERY Lemma/Theorem/Proposition in a
        .v file. Use this once before starting translation of a whole file
        to populate the oracle data for every proof at once.

        Args:
          coq_file: path to a .v file

        Returns:
          {
            "lemma_name_1": [{"theorem": "...", "args": [...]}, ...],
            "lemma_name_2": {"error": "..."},   # if extraction failed
            ...
          }
        """
        coq_file = _resolve(coq_file)
        return extract_resolved_calls_for_file(coq_file)

    return mcp


def _resolve(path: str) -> str:
    """Resolve relative paths against $GEOCOQ_DIR or the current working dir."""
    if os.path.isabs(path):
        return path
    root = os.environ.get("GEOCOQ_DIR")
    if root:
        candidate = os.path.join(root, path)
        if os.path.exists(candidate):
            return candidate
    return path


def main() -> None:
    mcp = _build_server()
    mcp.run()


if __name__ == "__main__":
    main()
