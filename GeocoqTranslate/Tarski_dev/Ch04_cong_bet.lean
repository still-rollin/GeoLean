/-
Translated from theories/Main/Tarski_dev/Ch04_cong_bet.v.

Statement-only translation (Phase 0). All proofs are `sorry`.

Lemmas combining congruence with betweenness (l4_2 through l4_6 and
`cong3_bet_eq`). All require decidable point equality.
-/

import GeocoqTranslate.Tarski.Axioms
import GeocoqTranslate.Tarski.Definitions
import GeocoqTranslate.Tarski_dev.Ch03_bet

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

section T3
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem l4_2 (A B C D A' B' C' D' : Tpoint)
    (h : IFSC A B C D A' B' C' D') : Cong B D B' D' := sorry

theorem l4_3 (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Cong A C A' C') (h₄ : Cong B C B' C') : Cong A B A' B' := sorry

theorem l4_3_1 (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Cong A B A' B') (h₄ : Cong A C A' C') : Cong B C B' C' := sorry

theorem l4_5 (A B C A' C' : Tpoint)
    (hBet : Bet A B C) (hCong : Cong A C A' C') :
    ∃ B', Bet A' B' C' ∧ Cong_3 A B C A' B' C' := sorry

theorem l4_6 (A B C A' B' C' : Tpoint)
    (hBet : Bet A B C) (hCong : Cong_3 A B C A' B' C') : Bet A' B' C' := sorry

theorem cong3_bet_eq (A B C X : Tpoint)
    (hBet : Bet A B C) (hCong : Cong_3 A B C A X C) : X = B := sorry

end T3

end GeocoqTranslate.Tarski
