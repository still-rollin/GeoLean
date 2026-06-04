/-
Translated from theories/Elements/OriginalProofs/lemma_congruenceflip.v.

  Cong A B C D → Cong B A D C ∧ Cong B A C D ∧ Cong A B D C

Three flips of a congruence, each one application of
`lemma_congruencetransitive` against `cn_equalityreverse`.
-/

import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencetransitive

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral

variable {Point : Type} [euclidean_neutral Point]

theorem lemma_congruenceflip (A B C D : Point) (h : Cong A B C D) :
    Cong B A D C ∧ Cong B A C D ∧ Cong A B D C := by
  have h_BAAB : Cong B A A B := cn_equalityreverse B A
  have h_CDDC : Cong C D D C := cn_equalityreverse C D
  have h_BACD : Cong B A C D := lemma_congruencetransitive B A A B C D h_BAAB h
  have h_ABDC : Cong A B D C := lemma_congruencetransitive A B C D D C h h_CDDC
  have h_BADC : Cong B A D C := lemma_congruencetransitive B A C D D C h_BACD h_CDDC
  exact ⟨h_BADC, h_BACD, h_ABDC⟩

end GeocoqTranslate.Elements
