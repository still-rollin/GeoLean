/-
Translated from theories/Elements/OriginalProofs/lemma_3_5b.v.

  BetS A B D → BetS B C D → BetS A C D

Two-step derivation: `axiom_innertransitivity` first yields `BetS A B C`,
then `lemma_3_7a` composes it with `BetS B C D` to get the goal.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_7a

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_3_5b (A B C D : Point)
    (h1 : BetS A B D) (h2 : BetS B C D) : BetS A C D := by
  have h3 : BetS A B C := axiom_innertransitivity A B C D h1 h2
  exact lemma_3_7a A B C D h3 h2

end GeocoqTranslate.Elements
