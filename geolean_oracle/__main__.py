"""CLI entry point: python -m geolean_oracle <coq_file> <lemma_name>"""

import argparse
import json
import sys

from src.oracle import extract_resolved_calls


def main():
    p = argparse.ArgumentParser(description="GeoLean translation oracle")
    p.add_argument("coq_file", help="path to a .v file under theories/")
    p.add_argument("lemma", help="lemma name to extract")
    p.add_argument("--json", action="store_true", help="emit JSON")
    p.add_argument("--show-proof-term", action="store_true",
                   help="also print the raw Show Proof output")
    args = p.parse_args()

    result = extract_resolved_calls(args.coq_file, args.lemma)

    if args.json:
        out = {
            "lemma_name": result.lemma_name,
            "proof_term": result.proof_term,
            "resolved_calls": [
                {"name": c.name, "args": c.args} for c in result.resolved_calls
            ],
        }
        json.dump(out, sys.stdout, indent=2)
        return

    print("=== RESOLVED CALLS ===")
    for c in result.resolved_calls:
        print(c.as_signature())
    if args.show_proof_term:
        print()
        print("=== PROOF TERM ===")
        print(result.proof_term)


if __name__ == "__main__":
    main()
