/-
Translated from theories/Elements/OriginalProofs/lemma_3_6b.v.

  BetS A B C → BetS A C D → BetS A B D

Reverse all three via `axiom_betweennesssymmetry`, apply `lemma_3_5b`
on the reversed triples, then reverse the conclusion back.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_5b

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_3_6b (A B C D : Point)
    (h1 : BetS A B C) (h2 : BetS A C D) : BetS A B D := by
  have h3 : BetS C B A := axiom_betweennesssymmetry A B C h1
  have h4 : BetS D C A := axiom_betweennesssymmetry A C D h2
  have h5 : BetS D B A := lemma_3_5b D C B A h4 h3
  exact axiom_betweennesssymmetry D B A h5

end GeocoqTranslate.Elements
