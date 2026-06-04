/-
Translated from theories/Elements/OriginalProofs/lemma_congruencesymmetric.v.

  Cong B C A D → Cong A D B C

Chains `cn_congruencereflexive` and `cn_congruencetransitive`.
-/

import GeocoqTranslate.Euclidean.Axioms

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral

variable {Point : Type} [euclidean_neutral Point]

theorem lemma_congruencesymmetric (A B C D : Point) (h : Cong B C A D) : Cong A D B C :=
  cn_congruencetransitive A D B C B C h (cn_congruencereflexive B C)

end GeocoqTranslate.Elements
