/-
Translated from theories/Elements/OriginalProofs/lemma_inequalitysymmetric.v.

  A ≠ B → B ≠ A

Trivial in Lean — equality symmetry. The Rocq proof goes through
`lemma_equalitysymmetric`; here we just contrapose `Eq.symm`.
-/

import GeocoqTranslate.Euclidean.Axioms

namespace GeocoqTranslate.Elements

variable {Point : Type}

theorem lemma_inequalitysymmetric (A B : Point) (h : A ≠ B) : B ≠ A :=
  fun h' => h h'.symm

end GeocoqTranslate.Elements
