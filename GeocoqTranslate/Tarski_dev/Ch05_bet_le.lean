/-
Translated from theories/Main/Tarski_dev/Ch05_bet_le.v.

Statement-only translation (Phase 0). All proofs are `sorry`.

Comparison of segments via `Le`/`Lt`/`Ge`/`Gt`. All under
`Tarski_neutral_dimensionless_with_decidable_point_equality`.
-/

import GeocoqTranslate.Tarski.Axioms
import GeocoqTranslate.Tarski.Definitions
import GeocoqTranslate.Tarski_dev.Ch04_col
import GeocoqTranslate.Tarski_dev.Ch04_cong_bet

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

section T5
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem l5_1 (A B C D : Tpoint) (hAB : A ≠ B)
    (h₁ : Bet A B C) (h₂ : Bet A B D) : Bet A C D ∨ Bet A D C := sorry

theorem l5_2 (A B C D : Tpoint) (hAB : A ≠ B)
    (h₁ : Bet A B C) (h₂ : Bet A B D) : Bet B C D ∨ Bet B D C := sorry

theorem segment_construction_2 (A Q B C : Tpoint) (hAQ : A ≠ Q) :
    ∃ X, (Bet Q A X ∨ Bet Q X A) ∧ Cong Q X B C := sorry

theorem l5_3 (A B C D : Tpoint)
    (h₁ : Bet A B D) (h₂ : Bet A C D) : Bet A B C ∨ Bet A C B := sorry

theorem bet3__bet (A B C D E : Tpoint)
    (h₁ : Bet A B E) (h₂ : Bet A D E) (h₃ : Bet B C D) : Bet A C E := sorry

theorem le_bet (A B C D : Tpoint) (h : Le C D A B) :
    ∃ X, Bet A X B ∧ Cong A X C D := sorry

theorem l5_5_1 (A B C D : Tpoint) (h : Le A B C D) :
    ∃ x, Bet A B x ∧ Cong A x C D := sorry

theorem l5_5_2 (A B C D : Tpoint)
    (h : ∃ x, Bet A B x ∧ Cong A x C D) : Le A B C D := sorry

theorem l5_6 (A B C D A' B' C' D' : Tpoint)
    (h₁ : Le A B C D) (h₂ : Cong A B A' B') (h₃ : Cong C D C' D') :
    Le A' B' C' D' := sorry

theorem le_reflexivity (A B : Tpoint) : Le A B A B := sorry

theorem le_transitivity (A B C D E F : Tpoint)
    (h₁ : Le A B C D) (h₂ : Le C D E F) : Le A B E F := sorry

theorem between_cong (A B C : Tpoint) (hBet : Bet A C B) (hCong : Cong A C A B) :
    C = B := sorry

theorem cong3_symmetry (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 A' B' C' A B C := sorry

theorem between_cong_2 (A B D E : Tpoint)
    (h₁ : Bet A D B) (h₂ : Bet A E B) (h₃ : Cong A D A E) : D = E := sorry

theorem between_cong_3 (A B D E : Tpoint) (hAB : A ≠ B)
    (h₁ : Bet A B D) (h₂ : Bet A B E) (h₃ : Cong B D B E) : D = E := sorry

theorem le_anti_symmetry (A B C D : Tpoint)
    (h₁ : Le A B C D) (h₂ : Le C D A B) : Cong A B C D := sorry

theorem cong_dec (A B C D : Tpoint) : Cong A B C D ∨ ¬ Cong A B C D := sorry

theorem bet_dec (A B C : Tpoint) : Bet A B C ∨ ¬ Bet A B C := sorry

theorem col_dec (A B C : Tpoint) : Col A B C ∨ ¬ Col A B C := sorry

theorem le_trivial (A C D : Tpoint) : Le A A C D := sorry

theorem le_cases (A B C D : Tpoint) : Le A B C D ∨ Le C D A B := sorry

theorem le_zero (A B C : Tpoint) (h : Le A B C C) : A = B := sorry

theorem le_diff (A B C D : Tpoint) (hAB : A ≠ B) (h : Le A B C D) : C ≠ D := sorry

theorem lt_diff (A B C D : Tpoint) (h : Lt A B C D) : C ≠ D := sorry

theorem bet_cong_eq (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C D) (h₃ : Cong B C A D) : C = D ∧ A = B := sorry

theorem cong__le (A B C D : Tpoint) (h : Cong A B C D) : Le A B C D := sorry

theorem cong__le3412 (A B C D : Tpoint) (h : Cong A B C D) : Le C D A B := sorry

theorem le1221 (A B : Tpoint) : Le A B B A := sorry

theorem le_left_comm (A B C D : Tpoint) (h : Le A B C D) : Le B A C D := sorry

theorem le_right_comm (A B C D : Tpoint) (h : Le A B C D) : Le A B D C := sorry

theorem le_comm (A B C D : Tpoint) (h : Le A B C D) : Le B A D C := sorry

theorem ge_left_comm (A B C D : Tpoint) (h : Ge A B C D) : Ge B A C D := sorry

theorem ge_right_comm (A B C D : Tpoint) (h : Ge A B C D) : Ge A B D C := sorry

theorem ge_comm (A B C D : Tpoint) (h : Ge A B C D) : Ge B A D C := sorry

theorem lt_right_comm (A B C D : Tpoint) (h : Lt A B C D) : Lt A B D C := sorry

theorem lt_left_comm (A B C D : Tpoint) (h : Lt A B C D) : Lt B A C D := sorry

theorem lt_comm (A B C D : Tpoint) (h : Lt A B C D) : Lt B A D C := sorry

theorem gt_left_comm (A B C D : Tpoint) (h : Gt A B C D) : Gt B A C D := sorry

theorem gt_right_comm (A B C D : Tpoint) (h : Gt A B C D) : Gt A B D C := sorry

theorem gt_comm (A B C D : Tpoint) (h : Gt A B C D) : Gt B A D C := sorry

theorem cong2_lt__lt (A B C D A' B' C' D' : Tpoint)
    (h₁ : Lt A B C D) (h₂ : Cong A B A' B') (h₃ : Cong C D C' D') :
    Lt A' B' C' D' := sorry

theorem fourth_point (A B C P : Tpoint)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCol : Col A B P) (hBet : Bet A B C) :
    Bet P A B ∨ Bet A P B ∨ Bet B P C ∨ Bet B C P := sorry

theorem third_point (A B P : Tpoint) (h : Col A B P) :
    Bet P A B ∨ Bet A P B ∨ Bet A B P := sorry

theorem l5_12_a (A B C : Tpoint) (h : Bet A B C) : Le A B A C ∧ Le B C A C := sorry

theorem bet__le1213 (A B C : Tpoint) (h : Bet A B C) : Le A B A C := sorry

theorem bet__le2313 (A B C : Tpoint) (h : Bet A B C) : Le B C A C := sorry

theorem bet__lt1213 (A B C : Tpoint) (hBC : B ≠ C) (h : Bet A B C) :
    Lt A B A C := sorry

theorem bet__lt2313 (A B C : Tpoint) (hAB : A ≠ B) (h : Bet A B C) :
    Lt B C A C := sorry

theorem l5_12_b (A B C : Tpoint)
    (hCol : Col A B C) (h₁ : Le A B A C) (h₂ : Le B C A C) : Bet A B C := sorry

theorem bet_le_eq (A B C : Tpoint)
    (hBet : Bet A B C) (hLe : Le A C B C) : A = B := sorry

theorem or_lt_cong_gt (A B C D : Tpoint) :
    Lt A B C D ∨ Gt A B C D ∨ Cong A B C D := sorry

theorem lt__le (A B C D : Tpoint) (h : Lt A B C D) : Le A B C D := sorry

theorem le1234_lt__lt (A B C D E F : Tpoint)
    (h₁ : Le A B C D) (h₂ : Lt C D E F) : Lt A B E F := sorry

theorem le3456_lt__lt (A B C D E F : Tpoint)
    (h₁ : Lt A B C D) (h₂ : Le C D E F) : Lt A B E F := sorry

theorem lt_transitivity (A B C D E F : Tpoint)
    (h₁ : Lt A B C D) (h₂ : Lt C D E F) : Lt A B E F := sorry

theorem not_and_lt (A B C D : Tpoint) : ¬ (Lt A B C D ∧ Lt C D A B) := sorry

theorem nlt (A B : Tpoint) : ¬ Lt A B A B := sorry

theorem le__nlt (A B C D : Tpoint) (h : Le A B C D) : ¬ Lt C D A B := sorry

theorem cong__nlt (A B C D : Tpoint) (h : Cong A B C D) : ¬ Lt A B C D := sorry

theorem nlt__le (A B C D : Tpoint) (h : ¬ Lt A B C D) : Le C D A B := sorry

theorem lt__nle (A B C D : Tpoint) (h : Lt A B C D) : ¬ Le C D A B := sorry

theorem nle__lt (A B C D : Tpoint) (h : ¬ Le A B C D) : Lt C D A B := sorry

theorem lt1123 (A B C : Tpoint) (hBC : B ≠ C) : Lt A A B C := sorry

theorem bet2_le2__le (O o A B a b : Tpoint)
    (h₁ : Bet a o b) (h₂ : Bet A O B)
    (h₃ : Le o a O A) (h₄ : Le o b O B) : Le a b A B := sorry

theorem Le_cases (A B C D : Tpoint)
    (h : Le A B C D ∨ Le B A C D ∨ Le A B D C ∨ Le B A D C) :
    Le A B C D := sorry

theorem Lt_cases (A B C D : Tpoint)
    (h : Lt A B C D ∨ Lt B A C D ∨ Lt A B D C ∨ Lt B A D C) :
    Lt A B C D := sorry

end T5

end GeocoqTranslate.Tarski
