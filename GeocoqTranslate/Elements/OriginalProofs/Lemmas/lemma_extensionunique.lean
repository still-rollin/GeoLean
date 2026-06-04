/-
Translated from theories/Elements/OriginalProofs/lemma_extensionunique.v.

  BetS A B E → BetS A B F → Cong B E B F → E = F

Apply `axiom_5_line` to derive `Cong E E E F`, symmetrise to
`Cong E F E E`, then `axiom_nocollapse` would give `E ≠ E` from `E ≠ F`,
contradicting `rfl`.
-/

import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral

variable {Point : Type} [euclidean_neutral Point]

theorem lemma_extensionunique (A B E F : Point)
    (h1 : BetS A B E) (h2 : BetS A B F) (h3 : Cong B E B F) : E = F := by
  have hBEBE : Cong B E B E := cn_congruencereflexive B E
  have hAEAE : Cong A E A E := cn_congruencereflexive A E
  have hABAB : Cong A B A B := cn_congruencereflexive A B
  have hEEEF : Cong E E E F := axiom_5_line A B E E A B F E h3 hAEAE hBEBE h1 h2 hABAB
  have hEFEE : Cong E F E E := lemma_congruencesymmetric E E E F hEEEF
  apply Classical.byContradiction
  intro hEF
  exact axiom_nocollapse E F E E hEF hEFEE rfl

end GeocoqTranslate.Elements
