/-
Translated from theories/Elements/OriginalProofs/lemma_localextension.v.

  A ≠ B → B ≠ Q → ∃ X, BetS A B X ∧ Cong B X B Q

Uses postulate_Euclid3 to build a circle of radius BQ centered at B,
postulate_line_circle to find the point on the AB-line + circle, then
axiom_circle_center_radius to derive the congruence.

Because `InCirc` is a plain `def` (Coq's `Definition` semantics), it
is not reducible by default. We use `show ∃ …` to unfold it explicitly
before constructing the value with the anonymous constructor.
-/

import GeocoqTranslate.Euclidean.Axioms

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_localextension (A B Q : Point) (hAB : A ≠ B) (hBQ : B ≠ Q) :
    ∃ X, BetS A B X ∧ Cong B X B Q := by
  obtain ⟨J, hCI⟩ := postulate_Euclid3 B Q hBQ
  have hInCirc : InCirc B J := by
    show ∃ X Y U V W : Point,
      CI J U V W ∧ (B = U ∨ (BetS U Y X ∧ Cong U X V W ∧ Cong U B U Y))
    exact ⟨B, B, B, B, Q, hCI, Or.inl rfl⟩
  obtain ⟨_, E, _, hBetS, _, hOnE, _⟩ :=
    postulate_line_circle A B B J B Q hCI hInCirc hAB
  exact ⟨E, hBetS, axiom_circle_center_radius B B Q J E hCI hOnE⟩

end GeocoqTranslate.Elements
