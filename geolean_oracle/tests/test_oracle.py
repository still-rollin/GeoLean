"""Smoke tests for the oracle. Run from repo root:

    python3 -m unittest geolean_oracle.tests.test_oracle

Requires that GeoCoq has been compiled with the current Coq:

    dune build theories/Elements/OriginalProofs/
"""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "geolean_oracle"))

from src.oracle import extract_resolved_calls  # noqa: E402

THEORIES = os.path.join(ROOT, "theories/Elements/OriginalProofs")


class TestOracle(unittest.TestCase):
    def test_lemma_3_6a(self):
        r = extract_resolved_calls(f"{THEORIES}/lemma_3_6a.v", "lemma_3_6a")
        calls = [c.as_signature() for c in r.resolved_calls]
        self.assertEqual(calls, [
            "axiom_betweennesssymmetry A B C H",
            "axiom_betweennesssymmetry A C D H0",
            "axiom_innertransitivity D C B A H2 H1",
            "axiom_betweennesssymmetry D C B H3",
        ])

    def test_lemma_3_7a(self):
        r = extract_resolved_calls(f"{THEORIES}/lemma_3_7a.v", "lemma_3_7a")
        calls = [c.as_signature() for c in r.resolved_calls]
        self.assertEqual(calls, [
            "lemma_betweennotequal A B C H",
            "lemma_betweennotequal B C D H0",
            "lemma_localextension A C D H1 H2",
            "lemma_congruencesymmetric C C E D H6",
            "lemma_3_6a A B C E H H5",
            "lemma_extensionunique B C D E H0 H8 H7",
        ])

    def test_lemma_3_7b(self):
        r = extract_resolved_calls(f"{THEORIES}/lemma_3_7b.v", "lemma_3_7b")
        calls = [c.as_signature() for c in r.resolved_calls]
        self.assertEqual(calls, [
            "axiom_betweennesssymmetry A B C H",
            "axiom_betweennesssymmetry B C D H0",
            "lemma_3_7a D C B A H2 H1",
            "axiom_betweennesssymmetry D B A H3",
        ])

    def test_proposition_01_shape(self):
        r = extract_resolved_calls(f"{THEORIES}/proposition_01.v", "proposition_01")
        names = [c.name for c in r.resolved_calls]
        # At least these landmark calls should appear.
        for expected in [
            "lemma_inequalitysymmetric",
            "lemma_localextension",
            "axiom_circle_center_radius",
            "lemma_congruencesymmetric",
            "lemma_congruenceflip",
            "axiom_nocollapse",
            "lemma_partnotequalwhole",
        ]:
            self.assertIn(expected, names, f"missing {expected} in proposition_01 trace")
        # Sanity: should be a substantial trace (~20+ calls).
        self.assertGreaterEqual(len(r.resolved_calls), 20)


if __name__ == "__main__":
    unittest.main()
