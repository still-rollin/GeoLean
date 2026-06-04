/-
Translated from theories/Elements/OriginalProofs/lemma_3_7b.v.

  BetS A B C → BetS B C D → BetS A B D

Symmetrise both hypotheses, apply lemma_3_7a, symmetrise the result.
-/

import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_7a

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_3_7b (A B C D : Point) (h1 : BetS A B C) (h2 : BetS B C D) :
    BetS A B D :=
  axiom_betweennesssymmetry D B A
    (lemma_3_7a D C B A
      (axiom_betweennesssymmetry B C D h2)
      (axiom_betweennesssymmetry A B C h1))

end GeocoqTranslate.Elements
