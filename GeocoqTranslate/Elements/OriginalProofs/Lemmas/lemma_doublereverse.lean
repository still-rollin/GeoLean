/-
Translated from theories/Elements/OriginalProofs/lemma_doublereverse.v.

  Cong A B C D → Cong D C B A ∧ Cong B A D C

Two flips of a congruence via `cn_equalityreverse` plus
`lemma_congruencetransitive` / `lemma_congruencesymmetric`.
-/

import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencetransitive
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral

variable {Point : Type} [euclidean_neutral Point]

theorem lemma_doublereverse (A B C D : Point) (h : Cong A B C D) :
    Cong D C B A ∧ Cong B A D C := by
  have h_CDDC : Cong C D D C := cn_equalityreverse C D
  have h_ABDC : Cong A B D C := lemma_congruencetransitive A B C D D C h h_CDDC
  have h_BAAB : Cong B A A B := cn_equalityreverse B A
  have h_BADC : Cong B A D C := lemma_congruencetransitive B A A B D C h_BAAB h_ABDC
  have h_DCBA : Cong D C B A := lemma_congruencesymmetric D B A C h_BADC
  exact ⟨h_DCBA, h_BADC⟩

end GeocoqTranslate.Elements
