/-
Translated from theories/Elements/OriginalProofs/euclidean_defs.v (subset
needed by Proposition 1). Additional defs added as later propositions
reach them.
-/

import GeocoqTranslate.Euclidean.Axioms

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis

variable {Point : Type} [euclidean_neutral_basis Point]

/-- Three points form an equilateral triangle: all three sides equal. -/
def equilateral (A B C : Point) : Prop :=
  Cong A B B C ∧ Cong B C C A

end GeocoqTranslate.Elements
