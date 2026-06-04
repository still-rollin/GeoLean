/-
Translated from theories/Elements/OriginalProofs/lemma_betweennotequal.v.

  BetS A B C → B ≠ C ∧ A ≠ B ∧ A ≠ C

Each ≠ is proved by `subst`-ing the equality into `h` and producing a
`BetS X Y X`-shaped term that contradicts `axiom_betweennessidentity`.
-/

import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_3_6a

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral

variable {Point : Type} [euclidean_neutral Point]

theorem lemma_betweennotequal (A B C : Point) (h : BetS A B C) :
    B ≠ C ∧ A ≠ B ∧ A ≠ C := by
  refine ⟨?_, ?_, ?_⟩
  · -- B ≠ C
    intro hBC
    subst hBC  -- C → B, h : BetS A B B
    exact axiom_betweennessidentity B B (lemma_3_6a A B B B h h)
  · -- A ≠ B
    intro hAB
    subst hAB  -- B → A, h : BetS A A C
    exact axiom_betweennessidentity A A (axiom_innertransitivity A A A C h h)
  · -- A ≠ C
    intro hAC
    subst hAC  -- C → A, h : BetS A B A
    exact axiom_betweennessidentity A B h

end GeocoqTranslate.Elements
