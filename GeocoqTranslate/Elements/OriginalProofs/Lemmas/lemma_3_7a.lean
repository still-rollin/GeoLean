/-
Translated from theories/Elements/OriginalProofs/lemma_3_7a.v.

  BetS A B C → BetS B C D → BetS A C D

Extend the AC-ray past C by length CD (lemma_localextension), get a
point E with BetS A C E and Cong C E C D. By lemma_3_6a, BetS B C E.
By extension-uniqueness on BetS B C D and BetS B C E with the
congruence, D = E. Substitute and we're done.
-/

import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_betweennotequal
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_localextension
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_extensionunique
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_6a

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_3_7a (A B C D : Point) (h1 : BetS A B C) (h2 : BetS B C D) :
    BetS A C D := by
  have hAneqC : A ≠ C := (lemma_betweennotequal A B C h1).2.2
  have hCneqD : C ≠ D := (lemma_betweennotequal B C D h2).1
  obtain ⟨E, hACE, hCECD⟩ := lemma_localextension A C D hAneqC hCneqD
  have hCDCE : Cong C D C E := lemma_congruencesymmetric C C E D hCECD
  have hBCE : BetS B C E := lemma_3_6a A B C E h1 hACE
  have hDE : D = E := lemma_extensionunique B C D E h2 hBCE hCDCE
  subst hDE
  exact hACE

end GeocoqTranslate.Elements
