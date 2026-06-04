/-
Translated from theories/Elements/OriginalProofs/lemma_congruencetransitive.v.

  Cong A B C D → Cong C D E F → Cong A B E F

Symmetrise the first hypothesis to feed `cn_congruencetransitive`.
-/

import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral

variable {Point : Type} [euclidean_neutral Point]

theorem lemma_congruencetransitive (A B C D E F : Point)
    (h1 : Cong A B C D) (h2 : Cong C D E F) : Cong A B E F :=
  cn_congruencetransitive A B E F C D (lemma_congruencesymmetric C A B D h1) h2

end GeocoqTranslate.Elements
