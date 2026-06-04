/-
Translated from theories/Axioms/Definitions.v (subset used by Ch02_cong).

Definitions building on `Tarski_neutral_dimensionless`. More definitions
from the same Rocq file will be added here as later chapters need them.
-/

import GeocoqTranslate.Tarski.Axioms

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless

variable {Tpoint : Type} [Tarski_neutral_dimensionless Tpoint]

/-- Definition 2.10: Outer Five Segment Configuration. -/
def OFSC (A B C D A' B' C' D' : Tpoint) : Prop :=
  Bet A B C ∧ Bet A' B' C' ∧
  Cong A B A' B' ∧ Cong B C B' C' ∧
  Cong A D A' D' ∧ Cong B D B' D'

/-- Definition 4.4: triangle congruence. -/
def Cong_3 (A B C A' B' C' : Tpoint) : Prop :=
  Cong A B A' B' ∧ Cong A C A' C' ∧ Cong B C B' C'

end GeocoqTranslate.Tarski
