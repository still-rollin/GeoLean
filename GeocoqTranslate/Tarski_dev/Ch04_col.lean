/-
Translated from theories/Main/Tarski_dev/Ch04_col.v.

Statement-only translation (Phase 0). All proofs are `sorry`.

Permutations and trivial cases of `Col` / `¬ Col`, plus the four core
collinearity lemmas (l4_13 through l4_19) used heavily downstream.
-/
import Mathlib.Tactic
import Mathlib.Tactic.Tauto
import Aesop
import GeocoqTranslate.Tarski.Axioms
import GeocoqTranslate.Tarski.Definitions
import GeocoqTranslate.Tarski_dev.Ch03_bet
import GeocoqTranslate.Tarski_dev.Ch04_cong_bet

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

/-! ## T4_1: Col permutations -/

section T4_1
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

@[aesop safe]
theorem col_permutation_1 (A B C : Tpoint) (h : Col A B C) : Col B C A := by
  unfold Col at h ⊢; tauto

@[aesop safe]
theorem col_permutation_2 (A B C : Tpoint) (h : Col A B C) : Col C A B := by
  unfold Col at h ⊢; tauto

@[aesop safe]
theorem col_permutation_3 (A B C : Tpoint) (h : Col A B C) : Col C B A := by
  unfold Col at h ⊢; rcases h with h | h | h <;> aesop

@[aesop safe]
theorem col_permutation_4 (A B C : Tpoint) (h : Col A B C) : Col B A C := by
  unfold Col at h ⊢; rcases h with h | h | h <;> aesop

@[aesop safe]
theorem col_permutation_5 (A B C : Tpoint) (h : Col A B C) : Col A C B := by
  unfold Col at h ⊢; rcases h with h | h | h <;> aesop

end T4_1

/-! ## T4_2: ¬ Col permutations -/

section T4_2
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem not_col_permutation_1 (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col B C A := fun h' => h (col_permutation_2 _ _ _ h')

theorem not_col_permutation_2 (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col C A B := fun h' => h (col_permutation_1 _ _ _ h')

theorem not_col_permutation_3 (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col C B A := fun h' => h (col_permutation_3 _ _ _ h')

theorem not_col_permutation_4 (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col B A C := fun h' => h (col_permutation_4 _ _ _ h')

theorem not_col_permutation_5 (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col A C B := fun h' => h (col_permutation_5 _ _ _ h')

end T4_2

/-! ## T4_3: case-split lemmas + trivial collinearity (neutral) -/

section T4_3
variable {Tpoint : Type} [Tarski_neutral_dimensionless Tpoint]

theorem Col_cases (A B C : Tpoint)
    (h : Col A B C ∨ Col A C B ∨ Col B A C ∨
         Col B C A ∨ Col C A B ∨ Col C B A) : Col A B C := sorry

theorem Col_perm (A B C : Tpoint) (h : Col A B C) :
    Col A B C ∧ Col A C B ∧ Col B A C ∧
    Col B C A ∧ Col C A B ∧ Col C B A := sorry

@[aesop safe]
theorem col_trivial_1 (A B : Tpoint) : Col A A B :=
  .inl (between_trivial2 A B)

@[aesop safe]
theorem col_trivial_2 (A B : Tpoint) : Col A B B :=
  .inl (between_trivial A B)

@[aesop safe]
theorem col_trivial_3 (A B : Tpoint) : Col A B A :=
  .inr (.inr (between_trivial2 A B))

end T4_3

/-! ## T4_4: main collinearity lemmas (Hilbert section IV.4) -/

section T4_4
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem l4_13 (A B C A' B' C' : Tpoint)
    (h₁ : Col A B C)
    (h₂ : Cong_3 A B C A' B' C') :
    Col A' B' C' := by
  obtain ⟨hAB, hAC, hBC⟩ := h₂
  rcases h₁ with hABC | hBCA | hCAB
  · exact .inl (l4_6 A B C A' B' C' hABC ⟨hAB, hAC, hBC⟩)
  · refine .inr (.inl ?_)
    exact l4_6 B C A B' C' A' hBCA
      ⟨hBC, cong_commutativity _ _ _ _ hAB, cong_commutativity _ _ _ _ hAC⟩
  · refine .inr (.inr ?_)
    exact l4_6 C A B C' A' B' hCAB
      ⟨cong_commutativity _ _ _ _ hAC, cong_commutativity _ _ _ _ hBC, hAB⟩


theorem l4_14 (A B C A' B' : Tpoint)
    (h₁ : Col A B C) (h₂ : Cong A B A' B') :
    ∃ C', Cong_3 A B C A' B' C' := sorry

theorem l4_16 (A B C D A' B' C' D' : Tpoint)
    (h₁ : FSC A B C D A' B' C' D') (hAB : A ≠ B) : Cong C D C' D' := sorry

theorem l4_17 (A B C P Q : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Cong A P A Q) (h₂ : Cong B P B Q) : Cong C P C Q := sorry

theorem l4_18 (A B C C' : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Cong A C A C') (h₂ : Cong B C B C') : C = C' := sorry

theorem l4_19 (A B C C' : Tpoint)
    (hBet : Bet A C B)
    (h₁ : Cong A C A C') (h₂ : Cong B C B C') : C = C' := sorry

theorem not_col_distincts (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col A B C ∧ A ≠ B ∧ B ≠ C ∧ A ≠ C := sorry

theorem NCol_cases (A B C : Tpoint)
    (h : ¬ Col A B C ∨ ¬ Col A C B ∨ ¬ Col B A C ∨
         ¬ Col B C A ∨ ¬ Col C A B ∨ ¬ Col C B A) : ¬ Col A B C := sorry

theorem NCol_perm (A B C : Tpoint) (h : ¬ Col A B C) :
    ¬ Col A B C ∧ ¬ Col A C B ∧ ¬ Col B A C ∧
    ¬ Col B C A ∧ ¬ Col C A B ∧ ¬ Col C B A := sorry

theorem col_cong_3_cong_3_eq (A B C A' B' C₁ C₂ : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B C)
    (h₁ : Cong_3 A B C A' B' C₁) (h₂ : Cong_3 A B C A' B' C₂) : C₁ = C₂ := sorry

end T4_4

end GeocoqTranslate.Tarski
