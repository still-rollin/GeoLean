/-
Translated from theories/Elements/OriginalProofs/lemma_3_6a.v.

  BetS A B C → BetS A C D → BetS B C D

Symmetrise both, apply axiom_innertransitivity, symmetrise again.
-/

import GeocoqTranslate.Euclidean.Axioms

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral

variable {Point : Type} [euclidean_neutral Point]

theorem lemma_3_6a (A B C D : Point) (h1 : BetS A B C) (h2 : BetS A C D) :
    BetS B C D :=
  axiom_betweennesssymmetry D C B
    (axiom_innertransitivity D C B A
      (axiom_betweennesssymmetry A C D h2)
      (axiom_betweennesssymmetry A B C h1))

end GeocoqTranslate.Elements
