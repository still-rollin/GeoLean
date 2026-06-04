/-
Translated from theories/Elements/OriginalProofs/lemma_partnotequalwhole.v.

  BetS A B C → ¬ Cong A B A C

If A, B, C are collinear with B strictly between A and C, then segment
AB cannot be congruent to AC. The proof extends BA past A to a point D
(postulate_Euclid2), notes that BetS D A B and BetS D A C both hold,
and applies extension-uniqueness: from Cong A B A C we would have B = C,
contradicting `lemma_betweennotequal`.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_inequalitysymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_betweennotequal
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_7b
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_extensionunique

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_partnotequalwhole (A B C : Point) (h : BetS A B C) :
    ¬ Cong A B A C := by
  have hAB : A ≠ B := (lemma_betweennotequal A B C h).2.1
  have hBA : B ≠ A := lemma_inequalitysymmetric A B hAB
  obtain ⟨D, hBAD⟩ := postulate_Euclid2 B A hBA
  have hDAB : BetS D A B := axiom_betweennesssymmetry B A D hBAD
  have hDAC : BetS D A C := lemma_3_7b D A B C hDAB h
  have hBC : B ≠ C := (lemma_betweennotequal A B C h).1
  intro hCong
  exact hBC (lemma_extensionunique D A B C hDAB hDAC hCong)

end GeocoqTranslate.Elements
