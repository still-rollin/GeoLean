/-
Translated from theories/Main/Tarski_dev/Ch06_out_lines.v.

Statement-only translation (Phase 0). All proofs are `sorry`.

Ray (`Out`) lemmas and column transitivity. All under
`Tarski_neutral_dimensionless_with_decidable_point_equality`.

Section T6_1: basic `Out` lemmas through `col2__eq`.
Section T6_2: existence, exchange, and collinearity-via-`Out` lemmas.

(The commented-out `t2_8` in the Rocq source is omitted here.)
-/

import GeocoqTranslate.Tarski.Axioms
import GeocoqTranslate.Tarski.Definitions
import GeocoqTranslate.Tarski_dev.Ch05_bet_le

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

/-! ## T6_1: ray basics -/

section T6_1
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem bet_out (A B C : Tpoint) (hBA : B ≠ A) (h : Bet A B C) : Out A B C := sorry

theorem bet_out_1 (A B C : Tpoint) (hBA : B ≠ A) (h : Bet C B A) : Out A B C := sorry

theorem out_dec (P A B : Tpoint) : Out P A B ∨ ¬ Out P A B := sorry

theorem out_diff1 (A B C : Tpoint) (h : Out A B C) : B ≠ A := sorry

theorem out_diff2 (A B C : Tpoint) (h : Out A B C) : C ≠ A := sorry

theorem out_distinct (A B C : Tpoint) (h : Out A B C) : B ≠ A ∧ C ≠ A := sorry

theorem out_col (A B C : Tpoint) (h : Out A B C) : Col A B C := sorry

theorem l6_2 (A B C P : Tpoint)
    (hAP : A ≠ P) (hBP : B ≠ P) (hCP : C ≠ P) (h : Bet A P C) :
    Bet B P C ↔ Out P A B := sorry

theorem bet_out__bet (A B C P : Tpoint) (h₁ : Bet A P C) (h₂ : Out P A B) :
    Bet B P C := sorry

theorem l6_3_1 (A B P : Tpoint) (h : Out P A B) :
    A ≠ P ∧ B ≠ P ∧ ∃ C, C ≠ P ∧ Bet A P C ∧ Bet B P C := sorry

theorem l6_3_2 (A B P : Tpoint)
    (h : A ≠ P ∧ B ≠ P ∧ ∃ C, C ≠ P ∧ Bet A P C ∧ Bet B P C) :
    Out P A B := sorry

theorem l6_4_1 (A B P : Tpoint) (h : Out P A B) : Col A P B ∧ ¬ Bet A P B := sorry

theorem l6_4_2 (A B P : Tpoint) (h : Col A P B ∧ ¬ Bet A P B) : Out P A B := sorry

theorem out_trivial (P A : Tpoint) (hAP : A ≠ P) : Out P A A := sorry

theorem l6_6 (P A B : Tpoint) (h : Out P A B) : Out P B A := sorry

theorem l6_7 (P A B C : Tpoint) (h₁ : Out P A B) (h₂ : Out P B C) : Out P A C := sorry

theorem bet_out_out_bet (A B C A' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Out B A A') (h₃ : Out B C C') : Bet A' B C' := sorry

theorem out2_bet_out (A B C X P : Tpoint)
    (h₁ : Out B A C) (h₂ : Out B X P) (h₃ : Bet A X C) :
    Out B A P ∧ Out B C P := sorry

theorem l6_11_uniqueness (A B C R X Y : Tpoint)
    (h₁ : Out A X R) (h₂ : Cong A X B C)
    (h₃ : Out A Y R) (h₄ : Cong A Y B C) : X = Y := sorry

theorem l6_11_existence (A B C R : Tpoint) (hRA : R ≠ A) (hBC : B ≠ C) :
    ∃ X, Out A X R ∧ Cong A X B C := sorry

theorem segment_construction_3 (A B X Y : Tpoint) (hAB : A ≠ B) (hXY : X ≠ Y) :
    ∃ C, Out A B C ∧ Cong A C X Y := sorry

theorem l6_13_1 (P A B : Tpoint) (h₁ : Out P A B) (h₂ : Le P A P B) :
    Bet P A B := sorry

theorem l6_13_2 (P A B : Tpoint) (h₁ : Out P A B) (h₂ : Bet P A B) :
    Le P A P B := sorry

theorem l6_16_1 (P Q S X : Tpoint) (hPQ : P ≠ Q)
    (h₁ : Col S P Q) (h₂ : Col X P Q) : Col X P S := sorry

theorem col_transitivity_1 (P Q A B : Tpoint) (hPQ : P ≠ Q)
    (h₁ : Col P Q A) (h₂ : Col P Q B) : Col P A B := sorry

theorem col_transitivity_2 (P Q A B : Tpoint) (hPQ : P ≠ Q)
    (h₁ : Col P Q A) (h₂ : Col P Q B) : Col Q A B := sorry

theorem l6_21 (A B C D P Q : Tpoint)
    (hNCol : ¬ Col A B C) (hCD : C ≠ D)
    (h₁ : Col A B P) (h₂ : Col A B Q)
    (h₃ : Col C D P) (h₄ : Col C D Q) : P = Q := sorry

theorem col2__eq (A B X Y : Tpoint)
    (h₁ : Col A X Y) (h₂ : Col B X Y) (h₃ : ¬ Col A X B) : X = Y := sorry

end T6_1

/-! ## T6_2: existence, exchange, collinearity via `Out` -/

section T6_2
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem not_col_exists (A B : Tpoint) (hAB : A ≠ B) : ∃ C, ¬ Col A B C := sorry

theorem col3 (X Y A B C : Tpoint) (hXY : X ≠ Y)
    (h₁ : Col X Y A) (h₂ : Col X Y B) (h₃ : Col X Y C) : Col A B C := sorry

theorem colx (A B C X Y : Tpoint) (hAB : A ≠ B)
    (h₁ : Col X Y A) (h₂ : Col X Y B) (h₃ : Col A B C) : Col X Y C := sorry

theorem out2__bet (A B C : Tpoint) (h₁ : Out A B C) (h₂ : Out C A B) : Bet A B C := sorry

theorem bet2_le2__le1346 (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le A B A' B') (h₄ : Le B C B' C') : Le A C A' C' := sorry

theorem bet2_le2__le2356 (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le A B A' B') (h₄ : Le A' C' A C) : Le B' C' B C := sorry

theorem bet2_le2__le1245 (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Le B C B' C') (h₄ : Le A' C' A C) : Le A' B' A B := sorry

theorem cong_preserves_bet (B A' A0 E D' D0 : Tpoint)
    (h₁ : Bet B A' A0) (h₂ : Cong B A' E D') (h₃ : Cong B A0 E D0)
    (h₄ : Out E D' D0) : Bet E D' D0 := sorry

theorem out_cong_cong (B A A0 E D D0 : Tpoint)
    (h₁ : Out B A A0) (h₂ : Out E D D0)
    (h₃ : Cong B A E D) (h₄ : Cong B A0 E D0) : Cong A A0 D D0 := sorry

theorem not_out_bet (A B C : Tpoint) (h₁ : Col A B C) (h₂ : ¬ Out B A C) :
    Bet A B C := sorry

theorem or_bet_out (A B C : Tpoint) : Bet A B C ∨ Out B A C ∨ ¬ Col A B C := sorry

theorem not_bet_out (A B C : Tpoint) (h₁ : Col A B C) (h₂ : ¬ Bet A B C) :
    Out B A C := sorry

theorem not_bet_and_out (A B C : Tpoint) : ¬ (Bet A B C ∧ Out B A C) := sorry

theorem out_to_bet (A B C A' B' C' : Tpoint)
    (h₁ : Col A' B' C')
    (h₂ : Out B A C ↔ Out B' A' C')
    (h₃ : Bet A B C) : Bet A' B' C' := sorry

theorem col_out2_col (A B C AA CC : Tpoint)
    (h₁ : Col A B C) (h₂ : Out B A AA) (h₃ : Out B C CC) : Col AA B CC := sorry

theorem bet2_out_out (A B C B' C' : Tpoint)
    (hBA : B ≠ A) (hB'A : B' ≠ A) (h₁ : Out A C C')
    (h₂ : Bet A B C) (h₃ : Bet A B' C') : Out A B B' := sorry

theorem bet2__out (A B C B' : Tpoint)
    (hAB : A ≠ B) (hAB' : A ≠ B')
    (h₁ : Bet A B C) (h₂ : Bet A B' C) : Out A B B' := sorry

theorem out_bet_out_1 (A B C P : Tpoint) (h₁ : Out P A C) (h₂ : Bet A B C) :
    Out P A B := sorry

theorem out_bet_out_2 (A B C P : Tpoint) (h₁ : Out P A C) (h₂ : Bet A B C) :
    Out P B C := sorry

theorem out_bet__out (A B P Q : Tpoint) (h₁ : Bet P Q A) (h₂ : Out Q A B) :
    Out P A B := sorry

theorem segment_reverse (A B C : Tpoint) (h : Bet A B C) :
    ∃ B', Bet A B' C ∧ Cong C B' A B := sorry

theorem diff_col_ex (A B : Tpoint) : ∃ C, A ≠ C ∧ B ≠ C ∧ Col A B C := sorry

theorem diff_bet_ex3 (A B C : Tpoint) (h : Bet A B C) :
    ∃ D, A ≠ D ∧ B ≠ D ∧ C ≠ D ∧ Col A B D := sorry

theorem diff_col_ex3 (A B C : Tpoint) (h : Col A B C) :
    ∃ D, A ≠ D ∧ B ≠ D ∧ C ≠ D ∧ Col A B D := sorry

theorem Out_cases (A B C : Tpoint) (h : Out A B C ∨ Out A C B) : Out A B C := sorry

end T6_2

end GeocoqTranslate.Tarski
