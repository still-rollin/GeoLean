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

/-- Inner Five Segment Configuration (Definitions.v line 21). -/
def IFSC (A B C D A' B' C' D' : Tpoint) : Prop :=
  Bet A B C ∧ Bet A' B' C' ∧
  Cong A C A' C' ∧ Cong B C B' C' ∧
  Cong A D A' D' ∧ Cong C D C' D'

/-- Definition 4.4: triangle congruence. -/
@[simp]
def Cong_3 (A B C A' B' C' : Tpoint) : Prop :=
  Cong A B A' B' ∧ Cong A C A' C' ∧ Cong B C B' C'

/-- Definition 4.10: collinearity. -/
@[simp]
def Col (A B C : Tpoint) : Prop :=
  Bet A B C ∨ Bet B C A ∨ Bet C A B

/-- Five-Segment Configuration with collinearity (Definitions.v line 47). -/
def FSC (A B C D A' B' C' D' : Tpoint) : Prop :=
  Col A B C ∧ Cong_3 A B C A' B' C' ∧ Cong A D A' D' ∧ Cong B D B' D'

/-- Four-point betweenness (used in Ch03 lemma `l3_9_4`). -/
def Bet_4 (A₁ A₂ A₃ A₄ : Tpoint) : Prop :=
  Bet A₁ A₂ A₃ ∧ Bet A₂ A₃ A₄ ∧ Bet A₁ A₂ A₄ ∧ Bet A₁ A₃ A₄

/-- Strict betweenness: `Bet` plus three distinctness conditions. -/
def BetS (A B C : Tpoint) : Prop :=
  Bet A B C ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C

/-- Definition 5.4: segment `AB ≤ CD` iff `AB` is congruent to a subsegment of `CD`. -/
def Le (A B C D : Tpoint) : Prop :=
  ∃ E, Bet C E D ∧ Cong A B C E

/-- `AB ≥ CD` iff `CD ≤ AB`. -/
def Ge (A B C D : Tpoint) : Prop := Le C D A B

/-- Strict comparison: `AB < CD` iff `AB ≤ CD` and `AB` not congruent to `CD`. -/
def Lt (A B C D : Tpoint) : Prop := Le A B C D ∧ ¬ Cong A B C D

/-- `AB > CD` iff `CD < AB`. -/
def Gt (A B C D : Tpoint) : Prop := Lt C D A B

/-- Definition 6.1: `Out P A B` — `A` and `B` lie on the same ray from `P`. -/
def Out (P A B : Tpoint) : Prop :=
  A ≠ P ∧ B ≠ P ∧ (Bet P A B ∨ Bet P B A)

/-- Definition 7.1: `Midpoint M A B` — `M` is between `A`, `B` with equal distances. -/
def Midpoint (M A B : Tpoint) : Prop := Bet A M B ∧ Cong A M M B

/-- Definition 8.1: `Per A B C` — angle at `B` is right (reflection of `C` over `B`
    is congruent to `A`). -/
def Per (A B C : Tpoint) : Prop := ∃ C', Midpoint B C C' ∧ Cong A C A C'

/-- Definition 8.11 (`X`-anchored form): line `AB` is perpendicular to line `CD` at `X`. -/
def Perp_at (X A B C D : Tpoint) : Prop :=
  A ≠ B ∧ C ≠ D ∧ Col X A B ∧ Col X C D ∧
  ∀ U V, Col U A B → Col V C D → Per U X V

/-- Definition 8.11: line `AB` is perpendicular to line `CD` (at some point). -/
def Perp (A B C D : Tpoint) : Prop := ∃ X, Perp_at X A B C D

/-- Definition 9.1: `TS A B P Q` — `P` and `Q` are on opposite sides of line `AB`. -/
def TS (A B P Q : Tpoint) : Prop :=
  ¬ Col P A B ∧ ¬ Col Q A B ∧ ∃ T, Col T A B ∧ Bet P T Q

/-- `OS A B P Q` — `P` and `Q` are on the same side of line `AB`. -/
def OS (A B P Q : Tpoint) : Prop := ∃ R, TS A B P R ∧ TS A B Q R

/-- Coplanarity of four points. -/
def Coplanar (A B C D : Tpoint) : Prop :=
  ∃ X, (Col A B X ∧ Col C D X) ∨
       (Col A C X ∧ Col B D X) ∨
       (Col A D X ∧ Col B C X)

/-- Definition 9.37: `P` and `Q` on opposite sides of plane `ABC`. -/
def TSP (A B C P Q : Tpoint) : Prop :=
  ¬ Coplanar A B C P ∧ ¬ Coplanar A B C Q ∧
  ∃ T, Coplanar A B C T ∧ Bet P T Q

/-- Definition 9.40: `P` and `Q` on the same side of plane `ABC`. -/
def OSP (A B C P Q : Tpoint) : Prop :=
  ∃ R, TSP A B C P R ∧ TSP A B C Q R

/-- Definition 10.3: `ReflectL P' P A B` — `P'` is the image of `P` under the
    reflection across line `AB`, in the form used for `A ≠ B`. -/
def ReflectL (P' P A B : Tpoint) : Prop :=
  (∃ X, Midpoint X P P' ∧ Col A B X) ∧ (Perp A B P P' ∨ P = P')

/-- Definition 10.3: `Reflect P' P A B` — `P'` is the reflection of `P` across
    line `AB` (handles the degenerate `A = B` case as a point reflection). -/
def Reflect (P' P A B : Tpoint) : Prop :=
  (A ≠ B ∧ ReflectL P' P A B) ∨ (A = B ∧ Midpoint A P P')

/-- Definition 10.3: `ReflectL_at M P' P A B` — anchored variant of `ReflectL`. -/
def ReflectL_at (M P' P A B : Tpoint) : Prop :=
  (Midpoint M P P' ∧ Col A B M) ∧ (Perp A B P P' ∨ P = P')

/-- Definition 10.3: `Reflect_at M P' P A B` — anchored variant of `Reflect`. -/
def Reflect_at (M P' P A B : Tpoint) : Prop :=
  (A ≠ B ∧ ReflectL_at M P' P A B) ∨ (A = B ∧ A = M ∧ Midpoint M P P')

/-- Saccheri quadrilateral `ABCD`: right angles at `A` and `D`, equal legs `AB = CD`,
    and `B`, `C` on the same side of `AD`. -/
def Saccheri (A B C D : Tpoint) : Prop :=
  Per B A D ∧ Per A D C ∧ Cong A B C D ∧ OS A D B C

end GeocoqTranslate.Tarski
