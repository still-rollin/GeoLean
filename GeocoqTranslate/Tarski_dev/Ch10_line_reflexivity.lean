/-
Translated from theories/Main/Tarski_dev/Ch10_line_reflexivity.v.

Statement-only translation (Phase 0). All proofs are `sorry`.

Line reflexivity: `Reflect` / `ReflectL` (reflection across a line) and their
anchored variants `Reflect_at` / `ReflectL_at`. All under section T10 in the
Rocq source with `Tarski_neutral_dimensionless_with_decidable_point_equality`.
-/

import Aesop
import GeocoqTranslate.Tarski.Axioms
import GeocoqTranslate.Tarski.Definitions
import GeocoqTranslate.Tarski_dev.Ch08_orthogonality
import GeocoqTranslate.Tarski_dev.Ch09_plane

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

section T10
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem ex_sym (A B X : Tpoint) :
    ∃ Y, (Perp A B X Y ∨ X = Y) ∧
         (∃ M, Col A B M ∧ Midpoint M X Y) := sorry

theorem is_image_is_image_spec (P P' A B : Tpoint) (hAB : A ≠ B) :
    Reflect P' P A B ↔ ReflectL P' P A B := sorry

theorem ex_sym1 (A B X : Tpoint) (hAB : A ≠ B) :
    ∃ Y, (Perp A B X Y ∨ X = Y) ∧
         (∃ M, Col A B M ∧ Midpoint M X Y ∧ Reflect X Y A B) := sorry

theorem l10_2_uniqueness (A B P P1 P2 : Tpoint)
    (h₁ : Reflect P1 P A B) (h₂ : Reflect P2 P A B) : P1 = P2 := sorry

theorem l10_2_uniqueness_spec (A B P P1 P2 : Tpoint)
    (h₁ : ReflectL P1 P A B) (h₂ : ReflectL P2 P A B) : P1 = P2 := sorry

theorem l10_2_existence_spec (A B P : Tpoint) :
    ∃ P', ReflectL P' P A B := sorry

theorem l10_2_existence (A B P : Tpoint) :
    ∃ P', Reflect P' P A B := sorry

theorem l10_4_spec (A B P P' : Tpoint) (h : ReflectL P P' A B) :
    ReflectL P' P A B := sorry

theorem l10_4 (A B P P' : Tpoint) (h : Reflect P P' A B) :
    Reflect P' P A B := sorry

theorem l10_5 (A B P P' P'' : Tpoint)
    (h₁ : Reflect P' P A B) (h₂ : Reflect P'' P' A B) : P = P'' := sorry

theorem l10_6_uniqueness (A B P P1 P2 : Tpoint)
    (h₁ : Reflect P P1 A B) (h₂ : Reflect P P2 A B) : P1 = P2 := sorry

theorem l10_6_uniqueness_spec (A B P P1 P2 : Tpoint)
    (h₁ : ReflectL P P1 A B) (h₂ : ReflectL P P2 A B) : P1 = P2 := sorry

theorem l10_6_existence_spec (A B P' : Tpoint) (hAB : A ≠ B) :
    ∃ P, ReflectL P' P A B := sorry

theorem l10_6_existence (A B P' : Tpoint) :
    ∃ P, Reflect P' P A B := sorry

theorem l10_7 (A B P P' Q Q' : Tpoint)
    (h₁ : Reflect P' P A B) (h₂ : Reflect Q' Q A B) (h₃ : P' = Q') : P = Q := sorry

theorem l10_8 (A B P : Tpoint) (h : Reflect P P A B) : Col P A B := sorry

theorem col__refl (A B P : Tpoint) (h : Col P A B) : ReflectL P P A B := sorry

theorem is_image_col_cong (A B P P' X : Tpoint) (hAB : A ≠ B)
    (h₁ : Reflect P P' A B) (h₂ : Col A B X) : Cong P X P' X := sorry

theorem is_image_spec_col_cong (A B P P' X : Tpoint)
    (h₁ : ReflectL P P' A B) (h₂ : Col A B X) : Cong P X P' X := sorry

theorem image_id (A B T T' : Tpoint) (hAB : A ≠ B)
    (hCol : Col A B T) (hRefl : Reflect T T' A B) : T = T' := sorry

theorem osym_not_col (A B P P' : Tpoint)
    (h₁ : Reflect P P' A B) (h₂ : ¬ Col A B P) : ¬ Col A B P' := sorry

theorem midpoint_preserves_image (A B P P' Q Q' M : Tpoint)
    (hAB : A ≠ B) (hCol : Col A B M) (hRefl : Reflect P P' A B)
    (h₁ : Midpoint M P Q) (h₂ : Midpoint M P' Q') : Reflect Q Q' A B := sorry

theorem image_in_is_image_spec (M A B P P' : Tpoint)
    (h : ReflectL_at M P P' A B) : ReflectL P P' A B := by
  obtain ⟨⟨hMid, hCol⟩, hPerp⟩ := h
  exact ⟨⟨M, hMid, hCol⟩, hPerp⟩

theorem image_in_gen_is_image (M A B P P' : Tpoint)
    (h : Reflect_at M P P' A B) : Reflect P P' A B := by
  rcases h with ⟨hAB, hSpec⟩ | ⟨hAB, hAM, hMid⟩
  · exact Or.inl ⟨hAB, image_in_is_image_spec M A B P P' hSpec⟩
  · exact Or.inr ⟨hAB, hAM.symm ▸ hMid⟩

theorem image_image_in (A B P P' M : Tpoint) (hPP' : P ≠ P')
    (h₁ : ReflectL P P' A B) (h₂ : Col A B M) (h₃ : Col P M P') :
    ReflectL_at M P P' A B := sorry

theorem image_in_col (A B P P' Y : Tpoint)
    (h : ReflectL_at Y P P' A B) : Col P P' Y := sorry

theorem is_image_spec_rev (P P' A B : Tpoint)
    (h : ReflectL P P' A B) : ReflectL P P' B A := sorry

theorem is_image_rev (P P' A B : Tpoint)
    (h : Reflect P P' A B) : Reflect P P' B A := sorry

theorem midpoint_preserves_per (A B C A1 B1 C1 M : Tpoint)
    (hPer : Per A B C)
    (h₁ : Midpoint M A A1) (h₂ : Midpoint M B B1) (h₃ : Midpoint M C C1) :
    Per A1 B1 C1 := sorry

theorem col__image_spec (A B X : Tpoint) (h : Col A B X) :
    ReflectL X X A B := sorry

theorem image_triv (A B : Tpoint) : Reflect A A A B := sorry

theorem cong_midpoint__image (A B X Y : Tpoint)
    (h₁ : Cong A X A Y) (h₂ : Midpoint B X Y) : Reflect Y X A B := sorry

theorem col_image_spec__eq (A B P P' : Tpoint)
    (h₁ : Col A B P) (h₂ : ReflectL P P' A B) : P = P' := sorry

theorem image_spec_triv (A B : Tpoint) : ReflectL A A B B := by
  refine ⟨⟨A, ?_, ?_⟩, Or.inr rfl⟩
  · exact ⟨between_trivial A A, cong_reflexivity A A⟩
  · exact Or.inl (between_trivial2 B A)

theorem image_spec__eq (A P P' : Tpoint) (h : ReflectL P P' A A) : P = P' := sorry

theorem image__midpoint (A P P' : Tpoint) (h : Reflect P P' A A) :
    Midpoint A P' P := by
  rcases h with ⟨hNE, _⟩ | ⟨_, hMid⟩
  · exact absurd rfl hNE
  · exact hMid

theorem is_image_spec_dec (A B C D : Tpoint) :
    ReflectL A B C D ∨ ¬ ReflectL A B C D := Classical.em _

theorem l10_14 (P P' A B : Tpoint) (hPP' : P ≠ P') (hAB : A ≠ B)
    (h : Reflect P P' A B) : TS A B P P' := sorry

theorem l10_15 (A B C P : Tpoint)
    (hCol : Col A B C) (hNCol : ¬ Col A B P) :
    ∃ Q, Perp A B Q C ∧ OS A B P Q := sorry

theorem ex_per_cong (A B C D X Y : Tpoint)
    (hAB : A ≠ B) (hXY : X ≠ Y) (hCol : Col A B C) (hNCol : ¬ Col A B D) :
    ∃ P, Per P C A ∧ Cong P C X Y ∧ OS A B P D := sorry

theorem exists_cong_per (A B X Y : Tpoint) :
    ∃ C, Per A B C ∧ Cong B C X Y := sorry

end T10

end GeocoqTranslate.Tarski
