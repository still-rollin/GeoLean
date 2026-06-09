/-
Translated from theories/Main/Tarski_dev/Ch07_midpoint.v.

Statement-only translation (Phase 0). All proofs are `sorry`.

Midpoint lemmas (`Midpoint`) and related collinearity-with-congruence
results. All under `Tarski_neutral_dimensionless_with_decidable_point_equality`.
-/

import GeocoqTranslate.Tarski.Axioms
import GeocoqTranslate.Tarski.Definitions
import GeocoqTranslate.Tarski_dev.Ch06_out_lines

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

/-! ## T7_1: midpoint basics -/

section T7_1
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem midpoint_dec (I A B : Tpoint) : Midpoint I A B ∨ ¬ Midpoint I A B := sorry

theorem is_midpoint_id (A B : Tpoint) (h : Midpoint A A B) : A = B := sorry

theorem is_midpoint_id_2 (A B : Tpoint) (h : Midpoint A B A) : A = B := sorry

theorem l7_2 (M A B : Tpoint) (h : Midpoint M A B) : Midpoint M B A := sorry

theorem l7_3 (M A : Tpoint) (h : Midpoint M A A) : M = A := sorry

theorem l7_3_2 (A : Tpoint) : Midpoint A A A := sorry

theorem symmetric_point_construction (P A : Tpoint) : ∃ P', Midpoint A P P' := sorry

theorem symmetric_point_uniqueness (A P P₁ P₂ : Tpoint)
    (h₁ : Midpoint P A P₁) (h₂ : Midpoint P A P₂) : P₁ = P₂ := sorry

theorem l7_9 (P Q A X : Tpoint) (h₁ : Midpoint A P X) (h₂ : Midpoint A Q X) :
    P = Q := sorry

theorem l7_9_bis (P Q A X : Tpoint) (h₁ : Midpoint A P X) (h₂ : Midpoint A X Q) :
    P = Q := sorry

theorem l7_13 (A P Q P' Q' : Tpoint)
    (h₁ : Midpoint A P' P) (h₂ : Midpoint A Q' Q) : Cong P Q P' Q' := sorry

theorem l7_15 (P Q R P' Q' R' A : Tpoint)
    (h₁ : Midpoint A P P') (h₂ : Midpoint A Q Q') (h₃ : Midpoint A R R')
    (h₄ : Bet P Q R) : Bet P' Q' R' := sorry

theorem l7_16 (P Q R S P' Q' R' S' A : Tpoint)
    (h₁ : Midpoint A P P') (h₂ : Midpoint A Q Q')
    (h₃ : Midpoint A R R') (h₄ : Midpoint A S S')
    (h₅ : Cong P Q R S) : Cong P' Q' R' S' := sorry

theorem symmetry_preserves_midpoint (A B C D E F Z : Tpoint)
    (h₁ : Midpoint Z A D) (h₂ : Midpoint Z B E)
    (h₃ : Midpoint Z C F) (h₄ : Midpoint B A C) : Midpoint E D F := sorry

end T7_1

/-! ## T7_2: midpoint uniqueness, existence, transport -/

section T7_2
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem Mid_cases (A B C : Tpoint) (h : Midpoint A B C ∨ Midpoint A C B) :
    Midpoint A B C := sorry

theorem Mid_perm (A B C : Tpoint) (h : Midpoint A B C) :
    Midpoint A B C ∧ Midpoint A C B := sorry

theorem l7_17 (P P' A B : Tpoint) (h₁ : Midpoint A P P') (h₂ : Midpoint B P P') :
    A = B := sorry

theorem l7_17_bis (P P' A B : Tpoint)
    (h₁ : Midpoint A P P') (h₂ : Midpoint B P' P) : A = B := sorry

theorem l7_20 (M A B : Tpoint) (hCol : Col A M B) (hCong : Cong M A M B) :
    A = B ∨ Midpoint M A B := sorry

theorem l7_20_bis (M A B : Tpoint) (hAB : A ≠ B)
    (hCol : Col A M B) (hCong : Cong M A M B) : Midpoint M A B := sorry

theorem cong_col_mid (A B C : Tpoint) (hAC : A ≠ C)
    (hCol : Col A B C) (hCong : Cong A B B C) : Midpoint B A C := sorry

theorem l7_21 (A B C D P : Tpoint)
    (hNCol : ¬ Col A B C) (hBD : B ≠ D)
    (h₁ : Cong A B C D) (h₂ : Cong B C D A)
    (h₃ : Col A P C) (h₄ : Col B P D) :
    Midpoint P A C ∧ Midpoint P B D := sorry

theorem l7_22_aux (A₁ A₂ B₁ B₂ C M₁ M₂ : Tpoint)
    (h₁ : Bet A₁ C A₂) (h₂ : Bet B₁ C B₂)
    (h₃ : Cong C A₁ C B₁) (h₄ : Cong C A₂ C B₂)
    (h₅ : Midpoint M₁ A₁ B₁) (h₆ : Midpoint M₂ A₂ B₂)
    (h₇ : Le C A₁ C A₂) : Bet M₁ C M₂ := sorry

theorem l7_22 (A₁ A₂ B₁ B₂ C M₁ M₂ : Tpoint)
    (h₁ : Bet A₁ C A₂) (h₂ : Bet B₁ C B₂)
    (h₃ : Cong C A₁ C B₁) (h₄ : Cong C A₂ C B₂)
    (h₅ : Midpoint M₁ A₁ B₁) (h₆ : Midpoint M₂ A₂ B₂) : Bet M₁ C M₂ := sorry

theorem bet_col1 (A B C D : Tpoint) (h₁ : Bet A B D) (h₂ : Bet A C D) :
    Col A B C := sorry

theorem l7_25 (A B C : Tpoint) (h : Cong C A C B) : ∃ X, Midpoint X A B := sorry

theorem midpoint_distinct_1 (I A B : Tpoint) (hAB : A ≠ B) (h : Midpoint I A B) :
    I ≠ A ∧ I ≠ B := sorry

theorem midpoint_distinct_2 (I A B : Tpoint) (hIA : I ≠ A) (h : Midpoint I A B) :
    A ≠ B ∧ I ≠ B := sorry

theorem midpoint_distinct_3 (I A B : Tpoint) (hIB : I ≠ B) (h : Midpoint I A B) :
    A ≠ B ∧ I ≠ A := sorry

theorem midpoint_def (A B C : Tpoint) (h₁ : Bet A B C) (h₂ : Cong A B B C) :
    Midpoint B A C := sorry

theorem midpoint_bet (A B C : Tpoint) (h : Midpoint B A C) : Bet A B C := sorry

theorem midpoint_col (A M B : Tpoint) (h : Midpoint M A B) : Col M A B := sorry

theorem midpoint_cong (A B C : Tpoint) (h : Midpoint B A C) : Cong A B B C := sorry

theorem midpoint_out (A B C : Tpoint) (hAC : A ≠ C) (h : Midpoint B A C) :
    Out A B C := sorry

theorem midpoint_out_1 (A B C : Tpoint) (hAC : A ≠ C) (h : Midpoint B A C) :
    Out C A B := sorry

theorem midpoint_not_midpoint (I A B : Tpoint) (hAB : A ≠ B) (h : Midpoint I A B) :
    ¬ Midpoint B A I := sorry

theorem swap_diff (A B : Tpoint) (h : A ≠ B) : B ≠ A := sorry

theorem cong_cong_half_1 (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Cong A B A' B') : Cong A M A' M' := sorry

theorem cong_cong_half_2 (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Cong A B A' B') : Cong B M B' M' := sorry

theorem cong_mid2__cong (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Cong A M A' M') : Cong A B A' B' := sorry

theorem mid__lt (A M B : Tpoint) (hAB : A ≠ B) (h : Midpoint M A B) :
    Lt A M A B := sorry

theorem le_mid2__le13 (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Le A M A' M') : Le A B A' B' := sorry

theorem le_mid2__le12 (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Le A B A' B') : Le A M A' M' := sorry

theorem lt_mid2__lt13 (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Lt A M A' M') : Lt A B A' B' := sorry

theorem lt_mid2__lt12 (A M B A' M' B' : Tpoint)
    (h₁ : Midpoint M A B) (h₂ : Midpoint M' A' B')
    (h₃ : Lt A B A' B') : Lt A M A' M' := sorry

theorem midpoint_preserves_out (A B C A' B' C' M : Tpoint)
    (h₀ : Out A B C)
    (h₁ : Midpoint M A A') (h₂ : Midpoint M B B') (h₃ : Midpoint M C C') :
    Out A' B' C' := sorry

theorem col_cong_bet (A B C D : Tpoint)
    (hCol : Col A B D) (hCong : Cong A B C D) (hBet : Bet A C B) :
    Bet C A D ∨ Bet C B D := sorry

theorem col_cong2_bet1 (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Cong A C B D) : Bet C B D := sorry

theorem col_cong2_bet2 (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Cong A D B C) : Bet C A D := sorry

theorem col_cong2_bet3 (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A B C)
    (h₁ : Cong A B C D) (h₂ : Cong A C B D) : Bet B C D := sorry

theorem col_cong2_bet4 (A B C D : Tpoint)
    (hCol : Col A B C) (hBet : Bet A B D)
    (h₁ : Cong A B C D) (h₂ : Cong A D B C) : Bet B D C := sorry

theorem col_bet2_cong1 (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Bet C B D) : Cong A C D B := sorry

theorem col_bet2_cong2 (A B C D : Tpoint)
    (hCol : Col A B D) (hBet : Bet A C B)
    (h₁ : Cong A B C D) (h₂ : Bet C A D) : Cong D A B C := sorry

theorem bet2_lt2__lt (O o A B a b : Tpoint)
    (h₁ : Bet a o b) (h₂ : Bet A O B)
    (h₃ : Lt o a O A) (h₄ : Lt o b O B) : Lt a b A B := sorry

theorem bet2_lt_le__lt (O o A B a b : Tpoint)
    (h₁ : Bet a o b) (h₂ : Bet A O B)
    (h₃ : Cong o a O A) (h₄ : Lt o b O B) : Lt a b A B := sorry

end T7_2

end GeocoqTranslate.Tarski
