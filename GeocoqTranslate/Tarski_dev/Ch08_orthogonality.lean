/-
Translated from theories/Main/Tarski_dev/Ch08_orthogonality.v.

Statement-only translation (Phase 0). All proofs are `sorry`.

Right angles (`Per`), perpendicular-at-a-point (`Perp_at`), and
perpendicularity (`Perp`). All under
`Tarski_neutral_dimensionless_with_decidable_point_equality`.

Sections T8_1 through T8_5 — kept as separate `section`s in Lean
to mirror the Rocq layout, though they all use the same instance.
-/

import GeocoqTranslate.Tarski.Axioms
import GeocoqTranslate.Tarski.Definitions
import GeocoqTranslate.Tarski_dev.Ch07_midpoint

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

/-! ## T8_1: `Per` decidability and basic symmetry -/

section T8_1
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem per_dec (A B C : Tpoint) : Per A B C ∨ ¬ Per A B C := sorry

theorem l8_2 (A B C : Tpoint) (h : Per A B C) : Per C B A := sorry

end T8_1

/-! ## T8_2: `Per` permutations and small lemmas -/

section T8_2
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem Per_cases (A B C : Tpoint) (h : Per A B C ∨ Per C B A) : Per A B C := sorry

theorem Per_perm (A B C : Tpoint) (h : Per A B C) : Per A B C ∧ Per C B A := sorry

theorem l8_3 (A B C A' : Tpoint)
    (h₁ : Per A B C) (hAB : A ≠ B) (hCol : Col B A A') : Per A' B C := sorry

theorem l8_4 (A B C C' : Tpoint) (h₁ : Per A B C) (h₂ : Midpoint B C C') :
    Per A B C' := sorry

theorem l8_5 (A B : Tpoint) : Per A B B := sorry

theorem l8_6 (A B C A' : Tpoint)
    (h₁ : Per A B C) (h₂ : Per A' B C) (h₃ : Bet A C A') : B = C := sorry

end T8_2

/-! ## T8_3: uniqueness, collinearity interactions -/

section T8_3
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem l8_7 (A B C : Tpoint) (h₁ : Per A B C) (h₂ : Per A C B) : B = C := sorry

theorem l8_8 (A B : Tpoint) (h : Per A B A) : A = B := sorry

theorem per_distinct (A B C : Tpoint) (h : Per A B C) (hAB : A ≠ B) : A ≠ C := sorry

theorem per_distinct_1 (A B C : Tpoint) (h : Per A B C) (hBC : B ≠ C) :
    A ≠ C := sorry

theorem l8_9 (A B C : Tpoint) (h₁ : Per A B C) (hCol : Col A B C) :
    A = B ∨ C = B := sorry

theorem l8_10 (A B C A' B' C' : Tpoint)
    (h₁ : Per A B C) (h₂ : Cong_3 A B C A' B' C') : Per A' B' C' := sorry

theorem col_col_per_per (A X C U V : Tpoint)
    (hAX : A ≠ X) (hCX : C ≠ X)
    (h₁ : Col U A X) (h₂ : Col V C X) (h₃ : Per A X C) : Per U X V := sorry

theorem perp_in_dec (X A B C D : Tpoint) :
    Perp_at X A B C D ∨ ¬ Perp_at X A B C D := sorry

theorem perp_distinct (A B C D : Tpoint) (h : Perp A B C D) :
    A ≠ B ∧ C ≠ D := sorry

theorem l8_12 (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X C D A B := sorry

theorem per_col (A B C D : Tpoint)
    (hBC : B ≠ C) (h₁ : Per A B C) (hCol : Col B C D) : Per A B D := sorry

theorem l8_13_2 (A B C D X : Tpoint)
    (hAB : A ≠ B) (hCD : C ≠ D) (hCol1 : Col X A B) (hCol2 : Col X C D)
    (h : ∃ U V : Tpoint, Col U A B ∧ Col V C D ∧ U ≠ X ∧ V ≠ X ∧ Per U X V) :
    Perp_at X A B C D := sorry

theorem l8_14_1 (A B : Tpoint) : ¬ Perp A B A B := sorry

theorem l8_14_2_1a (X A B C D : Tpoint) (h : Perp_at X A B C D) :
    Perp A B C D := sorry

theorem perp_in_distinct (X A B C D : Tpoint) (h : Perp_at X A B C D) :
    A ≠ B ∧ C ≠ D := sorry

theorem l8_14_2_1b (X A B C D Y : Tpoint)
    (h₁ : Perp_at X A B C D) (h₂ : Col Y A B) (h₃ : Col Y C D) : X = Y := sorry

theorem l8_14_2_1b_bis (A B C D X : Tpoint)
    (h₁ : Perp A B C D) (h₂ : Col X A B) (h₃ : Col X C D) :
    Perp_at X A B C D := sorry

theorem l8_14_2_2 (X A B C D : Tpoint)
    (h₁ : Perp A B C D)
    (h₂ : ∀ Y, Col Y A B → Col Y C D → X = Y) : Perp_at X A B C D := sorry

theorem l8_14_3 (A B C D X Y : Tpoint)
    (h₁ : Perp_at X A B C D) (h₂ : Perp_at Y A B C D) : X = Y := sorry

theorem l8_15_1 (A B C X : Tpoint) (hCol : Col A B X) (h : Perp A B C X) :
    Perp_at X A B C X := sorry

theorem l8_15_2 (A B C X : Tpoint) (hCol : Col A B X) (h : Perp_at X A B C X) :
    Perp A B C X := sorry

theorem perp_in_per (A B C : Tpoint) (h : Perp_at B A B B C) : Per A B C := sorry

theorem perp_sym (A B C D : Tpoint) (h : Perp A B C D) : Perp C D A B := sorry

theorem perp_col0 (A B C D X Y : Tpoint)
    (h₁ : Perp A B C D) (hXY : X ≠ Y) (hX : Col A B X) (hY : Col A B Y) :
    Perp C D X Y := sorry

theorem per_perp_in (A B C : Tpoint) (hAB : A ≠ B) (hBC : B ≠ C) (h : Per A B C) :
    Perp_at B A B B C := sorry

theorem per_perp (A B C : Tpoint) (hAB : A ≠ B) (hBC : B ≠ C) (h : Per A B C) :
    Perp A B B C := sorry

theorem perp_left_comm (A B C D : Tpoint) (h : Perp A B C D) :
    Perp B A C D := sorry

theorem perp_right_comm (A B C D : Tpoint) (h : Perp A B C D) :
    Perp A B D C := sorry

theorem perp_comm (A B C D : Tpoint) (h : Perp A B C D) : Perp B A D C := sorry

theorem perp_in_sym (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X C D A B := sorry

theorem perp_in_left_comm (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X B A C D := sorry

theorem perp_in_right_comm (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X A B D C := sorry

theorem perp_in_comm (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X B A D C := sorry

end T8_3

/-! ## T8_4: cases lemmas, collinearity preservation, key existence -/

section T8_4
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem Perp_cases (A B C D : Tpoint)
    (h : Perp A B C D ∨ Perp B A C D ∨ Perp A B D C ∨ Perp B A D C ∨
         Perp C D A B ∨ Perp C D B A ∨ Perp D C A B ∨ Perp D C B A) :
    Perp A B C D := sorry

theorem Perp_perm (A B C D : Tpoint) (h : Perp A B C D) :
    Perp A B C D ∧ Perp B A C D ∧ Perp A B D C ∧ Perp B A D C ∧
    Perp C D A B ∧ Perp C D B A ∧ Perp D C A B ∧ Perp D C B A := sorry

theorem Perp_in_cases (X A B C D : Tpoint)
    (h : Perp_at X A B C D ∨ Perp_at X B A C D ∨ Perp_at X A B D C ∨
         Perp_at X B A D C ∨ Perp_at X C D A B ∨ Perp_at X C D B A ∨
         Perp_at X D C A B ∨ Perp_at X D C B A) : Perp_at X A B C D := sorry

theorem Perp_in_perm (X A B C D : Tpoint) (h : Perp_at X A B C D) :
    Perp_at X A B C D ∧ Perp_at X B A C D ∧ Perp_at X A B D C ∧
    Perp_at X B A D C ∧ Perp_at X C D A B ∧ Perp_at X C D B A ∧
    Perp_at X D C A B ∧ Perp_at X D C B A := sorry

theorem perp_in_col (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Col A B X ∧ Col C D X := sorry

theorem perp_perp_in (A B C : Tpoint) (h : Perp A B C A) : Perp_at A A B C A := sorry

theorem perp_per_1 (A B C : Tpoint) (h : Perp A B C A) : Per B A C := sorry

theorem perp_per_2 (A B C : Tpoint) (h : Perp A B A C) : Per B A C := sorry

theorem perp_col (A B C D E : Tpoint)
    (hAE : A ≠ E) (h₁ : Perp A B C D) (h₂ : Col A B E) : Perp A E C D := sorry

theorem perp_col2 (A B C D X Y : Tpoint)
    (h₁ : Perp A B X Y) (hCD : C ≠ D) (hC : Col A B C) (hD : Col A B D) :
    Perp C D X Y := sorry

theorem perp_col4 (A B C D P Q R S : Tpoint)
    (hPQ : P ≠ Q) (hRS : R ≠ S)
    (h₁ : Col A B P) (h₂ : Col A B Q) (h₃ : Col C D R) (h₄ : Col C D S)
    (h : Perp A B C D) : Perp P Q R S := sorry

theorem perp_not_eq_1 (A B C D : Tpoint) (h : Perp A B C D) : A ≠ B := sorry

theorem perp_not_eq_2 (A B C D : Tpoint) (h : Perp A B C D) : C ≠ D := sorry

theorem diff_per_diff (A B P R : Tpoint)
    (hAB : A ≠ B) (h₁ : Cong A P B R) (h₂ : Per B A P) (h₃ : Per A B R) :
    P ≠ R := sorry

theorem per_not_colp (A B P R : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P) (hBR : B ≠ R)
    (h₁ : Per B A P) (h₂ : Per A B R) : ¬ Col P A R := sorry

theorem per_not_col (A B C : Tpoint)
    (hAB : A ≠ B) (hBC : B ≠ C) (h : Per A B C) : ¬ Col A B C := sorry

theorem perp_not_col2 (A B C D : Tpoint) (h : Perp A B C D) :
    ¬ Col A B C ∨ ¬ Col A B D := sorry

theorem perp_not_col (A B P : Tpoint) (h : Perp A B P A) : ¬ Col A B P := sorry

theorem perp_in_col_perp_in (A B C D E P : Tpoint)
    (hCE : C ≠ E) (hCol : Col C D E) (h : Perp_at P A B C D) :
    Perp_at P A B C E := sorry

theorem perp_col2_bis (A B C D P Q : Tpoint)
    (h₁ : Perp A B C D) (h₂ : Col C D P) (h₃ : Col C D Q) (hPQ : P ≠ Q) :
    Perp A B P Q := sorry

theorem perp_in_perp_bis (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp X B C D ∨ Perp A X C D := sorry

theorem col_per_perp (A B C D : Tpoint)
    (hAB : A ≠ B) (hBC : B ≠ C) (hDB : D ≠ B) (hDC : D ≠ C)
    (hCol : Col B C D) (h : Per A B C) : Perp C D A B := sorry

theorem per_cong_mid (A B C H : Tpoint)
    (hBC : B ≠ C) (h₁ : Bet A B C) (h₂ : Cong A H C H) (h₃ : Per H B C) :
    Midpoint B A C := sorry

theorem per_double_cong (A B C C' : Tpoint)
    (h₁ : Per A B C) (h₂ : Midpoint B C C') : Cong A C A C' := sorry

theorem cong_perp_or_mid (A B M X : Tpoint)
    (hAB : A ≠ B) (hM : Midpoint M A B) (h : Cong A X B X) :
    X = M ∨ ¬ Col A B X ∧ Perp_at M X M A B := sorry

theorem col_per2_cases (A B C D B' : Tpoint)
    (hBC : B ≠ C) (hB'C : B' ≠ C) (hCD : C ≠ D)
    (hCol : Col B C D) (h₁ : Per A B C) (h₂ : Per A B' C) :
    B = B' ∨ ¬ Col B' C D := sorry

theorem l8_16_1 (A B C U X : Tpoint)
    (hX : Col A B X) (hU : Col A B U) (h : Perp A B C X) :
    ¬ Col A B C ∧ Per C X U := sorry

theorem l8_16_2 (A B C U X : Tpoint)
    (hX : Col A B X) (hU : Col A B U) (hUX : U ≠ X)
    (hNCol : ¬ Col A B C) (h : Per C X U) : Perp A B C X := sorry

theorem l8_18_uniqueness (A B C X Y : Tpoint)
    (hNCol : ¬ Col A B C)
    (h₁ : Col A B X) (h₂ : Perp A B C X)
    (h₃ : Col A B Y) (h₄ : Perp A B C Y) : X = Y := sorry

theorem midpoint_distinct (A B X C C' : Tpoint)
    (hNCol : ¬ Col A B C) (hCol : Col A B X) (h : Midpoint X C C') :
    C ≠ C' := sorry

theorem l8_20_1 (A B C C' D P : Tpoint)
    (h₁ : Per A B C) (h₂ : Midpoint P C' D)
    (h₃ : Midpoint A C' C) (h₄ : Midpoint B D C) : Per B A P := sorry

theorem l8_20_2 (A B C C' D P : Tpoint)
    (h₁ : Per A B C) (h₂ : Midpoint P C' D)
    (h₃ : Midpoint A C' C) (h₄ : Midpoint B D C)
    (hBC : B ≠ C) : A ≠ P := sorry

theorem perp_col1 (A B C D X : Tpoint)
    (hCX : C ≠ X) (h₁ : Perp A B C D) (h₂ : Col C D X) : Perp A B C X := sorry

theorem l8_18_existence (A B C : Tpoint) (hNCol : ¬ Col A B C) :
    ∃ X, Col A B X ∧ Perp A B C X := sorry

theorem l8_21_aux (A B C : Tpoint) (hNCol : ¬ Col A B C) :
    ∃ P T, Perp A B P A ∧ Col A B T ∧ Bet C T P := sorry

theorem l8_21 (A B C : Tpoint) (hAB : A ≠ B) :
    ∃ P T, Perp A B P A ∧ Col A B T ∧ Bet C T P := sorry

theorem per_cong (A B P R X : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P)
    (h₁ : Per B A P) (h₂ : Per A B R) (h₃ : Cong A P B R)
    (hCol : Col A B X) (hBet : Bet P X R) : Cong A R P B := sorry

theorem perp_cong (A B P R X : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P)
    (h₁ : Perp A B P A) (h₂ : Perp A B R B) (h₃ : Cong A P B R)
    (hCol : Col A B X) (hBet : Bet P X R) : Cong A R P B := sorry

theorem perp_exists (O A B : Tpoint) (hAB : A ≠ B) : ∃ X, Perp O X A B := sorry

theorem perp_vector (A B : Tpoint) (hAB : A ≠ B) : ∃ X Y, Perp A B X Y := sorry

theorem midpoint_existence_aux (A B P Q T : Tpoint)
    (hAB : A ≠ B)
    (h₁ : Perp A B Q B) (h₂ : Perp A B P A)
    (h₃ : Col A B T) (h₄ : Bet Q T P) (h₅ : Le A P B Q) :
    ∃ X : Tpoint, Midpoint X A B := sorry

theorem midpoint_existence (A B : Tpoint) : ∃ X, Midpoint X A B := sorry

theorem perp_in_id (A B C X : Tpoint) (h : Perp_at X A B C A) : X = A := sorry

theorem l8_22 (A B P R X : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P)
    (h₁ : Per B A P) (h₂ : Per A B R) (h₃ : Cong A P B R)
    (hCol : Col A B X) (hBet : Bet P X R) :
    Cong A R P B ∧ Midpoint X A B ∧ Midpoint X P R := sorry

theorem l8_22_bis (A B P R X : Tpoint)
    (hAB : A ≠ B) (hAP : A ≠ P)
    (h₁ : Perp A B P A) (h₂ : Perp A B R B) (h₃ : Cong A P B R)
    (hCol : Col A B X) (hBet : Bet P X R) :
    Cong A R P B ∧ Midpoint X A B ∧ Midpoint X P R := sorry

theorem perp_in_perp (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Perp A B C D := sorry

end T8_4

/-! ## T8_5: projection lemmas -/

section T8_5
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem perp_proj (A B C D : Tpoint) (h₁ : Perp A B C D) (hNCol : ¬ Col A C D) :
    ∃ X, Col A B X ∧ Perp A X C D := sorry

theorem l8_24 (A B P Q R T : Tpoint)
    (h₁ : Perp P A A B) (h₂ : Perp Q B A B)
    (h₃ : Col A B T) (h₄ : Bet P T Q) (h₅ : Bet B R Q) (h₆ : Cong A P B R) :
    ∃ X, Midpoint X A B ∧ Midpoint X P R := sorry

theorem col_per2__per (A B C P X : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Per A X P) (h₂ : Per B X P) : Per C X P := sorry

theorem perp_in_per_1 (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per A X C := sorry

theorem perp_in_per_2 (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per A X D := sorry

theorem perp_in_per_3 (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per B X C := sorry

theorem perp_in_per_4 (A B C D X : Tpoint) (h : Perp_at X A B C D) :
    Per B X D := sorry

end T8_5

end GeocoqTranslate.Tarski
