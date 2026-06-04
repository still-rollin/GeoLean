/-
Translated from theories/Main/Tarski_dev/Ch02_cong.v.

Section 1: basic facts about congruence — equivalence, permutations,
trivial identity, segment construction uniqueness.

Sections T1_1 through T1_3 use only `Tarski_neutral_dimensionless`;
T1_4 lemmas additionally need point-equality decidability.
-/

import GeocoqTranslate.Tarski.Axioms
import GeocoqTranslate.Tarski.Definitions

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

/-! ## T1_1: congruence basics -/

section T1_1
variable {Tpoint : Type} [Tarski_neutral_dimensionless Tpoint]

theorem cong_reflexivity (A B : Tpoint) : Cong A B A B :=
  cong_inner_transitivity B A A B A B
    (cong_pseudo_reflexivity B A)
    (cong_pseudo_reflexivity B A)

theorem cong_symmetry (A B C D : Tpoint) (h : Cong A B C D) : Cong C D A B :=
  cong_inner_transitivity A B C D A B h (cong_reflexivity A B)

theorem cong_transitivity (A B C D E F : Tpoint)
    (h1 : Cong A B C D) (h2 : Cong C D E F) : Cong A B E F :=
  cong_inner_transitivity C D A B E F (cong_symmetry A B C D h1) h2

theorem cong_left_commutativity (A B C D : Tpoint)
    (h : Cong A B C D) : Cong B A C D :=
  cong_inner_transitivity A B B A C D (cong_pseudo_reflexivity A B) h

theorem cong_right_commutativity (A B C D : Tpoint)
    (h : Cong A B C D) : Cong A B D C :=
  cong_symmetry D C A B
    (cong_left_commutativity C D A B
      (cong_symmetry A B C D h))

theorem cong_3421 (A B C D : Tpoint) (h : Cong A B C D) : Cong C D B A :=
  cong_right_commutativity C D A B (cong_symmetry A B C D h)

theorem cong_4312 (A B C D : Tpoint) (h : Cong A B C D) : Cong D C A B :=
  cong_left_commutativity C D A B (cong_symmetry A B C D h)

theorem cong_4321 (A B C D : Tpoint) (h : Cong A B C D) : Cong D C B A :=
  cong_right_commutativity D C A B (cong_4312 A B C D h)

theorem cong_trivial_identity (A B : Tpoint) : Cong A A B B := by
  obtain ⟨E, _, hCong⟩ := segment_construction B A B B
  have hAE : A = E := cong_identity A E B hCong
  exact hAE.symm ▸ hCong

theorem cong_reverse_identity (A C D : Tpoint) (h : Cong A A C D) : C = D :=
  cong_identity C D A (cong_symmetry A A C D h)

theorem cong_commutativity (A B C D : Tpoint) (h : Cong A B C D) : Cong B A D C :=
  cong_left_commutativity A B D C (cong_right_commutativity A B C D h)

end T1_1

/-! ## T1_2: negated-congruence permutations -/

section T1_2
variable {Tpoint : Type} [Tarski_neutral_dimensionless Tpoint]

theorem not_cong_2134 (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong B A C D :=
  fun h' => h (cong_left_commutativity B A C D h')

theorem not_cong_1243 (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong A B D C :=
  fun h' => h (cong_right_commutativity A B D C h')

theorem not_cong_2143 (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong B A D C :=
  fun h' => h (cong_commutativity B A D C h')

theorem not_cong_3412 (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong C D A B :=
  fun h' => h (cong_symmetry C D A B h')

theorem not_cong_4312 (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong D C A B :=
  fun h' => h (cong_symmetry C D A B (cong_left_commutativity D C A B h'))

theorem not_cong_3421 (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong C D B A :=
  fun h' => h (cong_symmetry C D A B (cong_right_commutativity C D B A h'))

theorem not_cong_4321 (A B C D : Tpoint) (h : ¬ Cong A B C D) : ¬ Cong D C B A :=
  fun h' => h (cong_4321 D C B A h')

end T1_2

/-! ## T1_3: five-segment and triangle congruence -/

section T1_3
variable {Tpoint : Type} [Tarski_neutral_dimensionless Tpoint]

theorem five_segment_with_def (A B C D A' B' C' D' : Tpoint)
    (h : OFSC A B C D A' B' C' D') (hAB : A ≠ B) : Cong C D C' D' := by
  obtain ⟨hBet, hBet', hABA'B', hBCB'C', hADA'D', hBDB'D'⟩ := h
  exact five_segment A A' B B' C C' D D' hABA'B' hBCB'C' hADA'D' hBDB'D' hBet hBet' hAB

theorem cong_diff (A B C D : Tpoint) (hAB : A ≠ B) (h : Cong A B C D) : C ≠ D := by
  intro hCD
  exact hAB (cong_identity A B C (hCD.symm ▸ h))

theorem cong_diff_2 (A B C D : Tpoint) (hBA : B ≠ A) (h : Cong A B C D) : C ≠ D := by
  intro hCD
  exact hBA (cong_identity A B C (hCD.symm ▸ h)).symm

theorem cong_diff_3 (A B C D : Tpoint) (hCD : C ≠ D) (h : Cong A B C D) : A ≠ B := by
  intro hAB
  subst hAB
  exact hCD (cong_identity C D A (cong_symmetry A A C D h))

theorem cong_diff_4 (A B C D : Tpoint) (hDC : D ≠ C) (h : Cong A B C D) : A ≠ B := by
  intro hAB
  subst hAB
  exact hDC (cong_identity C D A (cong_symmetry A A C D h)).symm

theorem cong_3_sym (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 A' B' C' A B C := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨cong_symmetry _ _ _ _ h1, cong_symmetry _ _ _ _ h2, cong_symmetry _ _ _ _ h3⟩

theorem cong_3_swap (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 B A C B' A' C' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨cong_commutativity _ _ _ _ h1, h3, h2⟩

theorem cong_3_swap_2 (A B C A' B' C' : Tpoint) (h : Cong_3 A B C A' B' C') :
    Cong_3 A C B A' C' B' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h2, h1, cong_commutativity _ _ _ _ h3⟩

theorem cong3_transitivity (A0 B0 C0 A1 B1 C1 A2 B2 C2 : Tpoint)
    (h1 : Cong_3 A0 B0 C0 A1 B1 C1) (h2 : Cong_3 A1 B1 C1 A2 B2 C2) :
    Cong_3 A0 B0 C0 A2 B2 C2 := by
  obtain ⟨h1a, h1b, h1c⟩ := h1
  obtain ⟨h2a, h2b, h2c⟩ := h2
  exact ⟨cong_transitivity _ _ _ _ _ _ h1a h2a,
         cong_transitivity _ _ _ _ _ _ h1b h2b,
         cong_transitivity _ _ _ _ _ _ h1c h2c⟩

end T1_3

/-! ## T1_4: needs decidable point equality -/

section T1_4
variable {Tpoint : Type} [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem eq_dec_points (A B : Tpoint) : A = B ∨ A ≠ B :=
  point_equality_decidability A B

theorem distinct (P Q R : Tpoint) (hPQ : P ≠ Q) : R ≠ P ∨ R ≠ Q := by
  rcases eq_dec_points R P with hRP | hRP
  · subst hRP
    exact Or.inr hPQ
  · exact Or.inl hRP

theorem l2_11 (A B C A' B' C' : Tpoint)
    (h1 : Bet A B C) (h2 : Bet A' B' C')
    (h3 : Cong A B A' B') (h4 : Cong B C B' C') : Cong A C A' C' := by
  rcases eq_dec_points A B with hAB | hAB
  · subst hAB
    have hA'B' : A' = B' := cong_identity A' B' A (cong_symmetry A A A' B' h3)
    subst hA'B'
    exact h4
  · exact cong_commutativity C A C' A'
      (five_segment A A' B B' C C' A A'
        h3 h4
        (cong_trivial_identity A A')
        (cong_commutativity A B A' B' h3)
        h1 h2 hAB)

theorem bet_cong3 (A B C A' B' : Tpoint)
    (h1 : Bet A B C) (h2 : Cong A B A' B') : ∃ C', Cong_3 A B C A' B' C' := by
  obtain ⟨x, hBet, hCong⟩ := segment_construction A' B' B C
  have hBCBx : Cong B C B' x := cong_symmetry B' x B C hCong
  exact ⟨x, h2, l2_11 A B C A' B' x h1 hBet h2 hBCBx, hBCBx⟩

theorem construction_uniqueness (Q A B C X Y : Tpoint)
    (hQA : Q ≠ A) (hBet1 : Bet Q A X) (hCong1 : Cong A X B C)
    (hBet2 : Bet Q A Y) (hCong2 : Cong A Y B C) : X = Y := by
  have hAXAY : Cong A X A Y :=
    cong_transitivity A X B C A Y hCong1 (cong_symmetry A Y B C hCong2)
  have hQXQY : Cong Q X Q Y :=
    l2_11 Q A X Q A Y hBet1 hBet2 (cong_reflexivity Q A) hAXAY
  have hOFSC : OFSC Q A X Y Q A X X :=
    ⟨hBet1, hBet1, cong_reflexivity Q A, cong_reflexivity A X,
     cong_symmetry Q X Q Y hQXQY, cong_symmetry A X A Y hAXAY⟩
  exact cong_identity X Y X (five_segment_with_def Q A X Y Q A X X hOFSC hQA)

theorem Cong_cases (A B C D : Tpoint)
    (h : Cong A B C D ∨ Cong A B D C ∨ Cong B A C D ∨ Cong B A D C ∨
         Cong C D A B ∨ Cong C D B A ∨ Cong D C A B ∨ Cong D C B A) :
    Cong A B C D := by
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · exact cong_right_commutativity A B D C h
  · exact cong_left_commutativity B A C D h
  · exact cong_commutativity B A D C h
  · exact cong_symmetry C D A B h
  · exact cong_symmetry C D A B (cong_right_commutativity C D B A h)
  · exact cong_symmetry C D A B (cong_left_commutativity D C A B h)
  · exact cong_4321 D C B A h

theorem Cong_perm (A B C D : Tpoint) (h : Cong A B C D) :
    Cong A B C D ∧ Cong A B D C ∧ Cong B A C D ∧ Cong B A D C ∧
    Cong C D A B ∧ Cong C D B A ∧ Cong D C A B ∧ Cong D C B A :=
  ⟨h,
   cong_right_commutativity A B C D h,
   cong_left_commutativity A B C D h,
   cong_commutativity A B C D h,
   cong_symmetry A B C D h,
   cong_3421 A B C D h,
   cong_4312 A B C D h,
   cong_4321 A B C D h⟩

end T1_4

end GeocoqTranslate.Tarski
