/-
Translated from theories/Elements/OriginalProofs/lemma_NCdistinct.v.

  nCol A B C →
    A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ B ≠ A ∧ C ≠ B ∧ C ≠ A

Trivial in Lean: three of the six inequalities are literal components of
`nCol`; the other three follow from `Ne.symm`.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_inequalitysymmetric

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis

variable {Point : Type} [euclidean_neutral_basis Point]

theorem lemma_NCdistinct (A B C : Point) (h : nCol A B C) :
    A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ B ≠ A ∧ C ≠ B ∧ C ≠ A := by
  obtain ⟨hAB, hAC, hBC, _, _, _⟩ := h
  exact ⟨hAB, hBC, hAC, fun h => hAB h.symm,
         fun h => hBC h.symm, fun h => hAC h.symm⟩

end GeocoqTranslate.Elements
