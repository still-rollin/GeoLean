/-
Translated from theories/Main/Tarski_dev/Ch09_plane.v.

Statement-only translation (Phase 0). All proofs are `sorry`.

Two-sides (`TS`), one-side (`OS`), coplanarity (`Coplanar`), and their
3D analogues `TSP` / `OSP`. All under section T9 in the Rocq source
with `Tarski_neutral_dimensionless_with_decidable_point_equality`.

Note: the Rocq lemma `sym_sym` (line 362) is commented out upstream
and references the undefined identifier `ReflectP`; omitted here.
-/

import GeocoqTranslate.Tarski.Axioms
import GeocoqTranslate.Tarski.Definitions
import GeocoqTranslate.Tarski_dev.Ch08_orthogonality

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

section T9
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem ts_distincts (A B P Q : Tpoint) (h : TS A B P Q) :
    A ≠ B ∧ A ≠ P ∧ A ≠ Q ∧ B ≠ P ∧ B ≠ Q ∧ P ≠ Q := sorry

theorem l9_2 (A B P Q : Tpoint) (h : TS A B P Q) : TS A B Q P := sorry

theorem mid_preserves_col (A B C M A' B' C' : Tpoint)
    (hCol : Col A B C) (h₁ : Midpoint M A A')
    (h₂ : Midpoint M B B') (h₃ : Midpoint M C C') : Col A' B' C' := sorry

theorem per_mid_per (A B X Y M : Tpoint)
    (hAB : A ≠ B) (h₁ : Per X A B)
    (h₂ : Midpoint M A B) (h₃ : Midpoint M X Y) :
    Cong A X B Y ∧ Per Y B A := sorry

theorem sym_preserve_diff (A B M A' B' : Tpoint)
    (hAB : A ≠ B) (h₁ : Midpoint M A A') (h₂ : Midpoint M B B') :
    A' ≠ B' := sorry

theorem l9_4_1_aux (P Q A C R S M : Tpoint)
    (hLe : Le S C R A) (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hMid : Midpoint M R S) :
    ∀ U C', Midpoint M U C' → (Out R U A ↔ Out S C C') := sorry

theorem per_col_eq (A B C : Tpoint)
    (h₁ : Per A B C) (hCol : Col A B C) (hBC : B ≠ C) : A = B := sorry

theorem l9_4_1 (P Q A C R S M : Tpoint)
    (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hMid : Midpoint M R S) :
    ∀ U C', Midpoint M U C' → (Out R U A ↔ Out S C C') := sorry

theorem mid_two_sides (A B M X Y : Tpoint)
    (h₁ : Midpoint M A B) (hNCol : ¬ Col A B X) (h₂ : Midpoint M X Y) :
    TS A B X Y := sorry

theorem col_preserves_two_sides (A B C D X Y : Tpoint)
    (hCD : C ≠ D) (h₁ : Col A B C) (h₂ : Col A B D) (h : TS A B X Y) :
    TS C D X Y := sorry

theorem out_out_two_sides (A B X Y U V I : Tpoint)
    (hAB : A ≠ B) (h₁ : TS A B X Y)
    (hCol1 : Col I A B) (hCol2 : Col I X Y)
    (hOut1 : Out I X U) (hOut2 : Out I Y V) : TS A B U V := sorry

theorem l9_4_2_aux (P Q A C R S U V : Tpoint)
    (hLe : Le S C R A) (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hOutU : Out R U A) (hOutV : Out S V C) : TS P Q U V := sorry

theorem l9_4_2 (P Q A C R S U V : Tpoint)
    (h₁ : TS P Q A C)
    (hR : Col R P Q) (hPerpA : Perp P Q A R)
    (hS : Col S P Q) (hPerpC : Perp P Q C S)
    (hOutU : Out R U A) (hOutV : Out S V C) : TS P Q U V := sorry

theorem l9_5 (P Q A C R B : Tpoint)
    (h₁ : TS P Q A C) (hR : Col R P Q) (hOut : Out R A B) : TS P Q B C := sorry

theorem outer_pasch (A B C P Q : Tpoint) (h₁ : Bet A C P) (h₂ : Bet B Q C) :
    ∃ X, Bet A X B ∧ Bet P Q X := sorry

theorem os_distincts (A B X Y : Tpoint) (h : OS A B X Y) :
    A ≠ B ∧ A ≠ X ∧ A ≠ Y ∧ B ≠ X ∧ B ≠ Y := sorry

theorem invert_one_side (A B P Q : Tpoint) (h : OS A B P Q) : OS B A P Q := sorry

theorem l9_8_1 (P Q A B C : Tpoint) (h₁ : TS P Q A C) (h₂ : TS P Q B C) :
    OS P Q A B := sorry

theorem not_two_sides_id (A P Q : Tpoint) : ¬ TS P Q A A := sorry

theorem l9_8_2 (P Q A B C : Tpoint) (h₁ : TS P Q A C) (h₂ : OS P Q A B) :
    TS P Q B C := sorry

theorem l9_9 (P Q A B : Tpoint) (h : TS P Q A B) : ¬ OS P Q A B := sorry

theorem l9_9_bis (P Q A B : Tpoint) (h : OS P Q A B) : ¬ TS P Q A B := sorry

theorem one_side_chara (P Q A B : Tpoint) (h : OS P Q A B) :
    ∀ X, Col X P Q → ¬ Bet A X B := sorry

theorem l9_10 (P Q A : Tpoint) (hNCol : ¬ Col A P Q) : ∃ C, TS P Q A C := sorry

theorem one_side_reflexivity (P Q A : Tpoint) (hNCol : ¬ Col A P Q) :
    OS P Q A A := sorry

theorem one_side_symmetry (P Q A B : Tpoint) (h : OS P Q A B) :
    OS P Q B A := sorry

theorem one_side_transitivity (P Q A B C : Tpoint)
    (h₁ : OS P Q A B) (h₂ : OS P Q B C) : OS P Q A C := sorry

theorem l9_17 (A B C P Q : Tpoint) (h₁ : OS P Q A C) (h₂ : Bet A B C) :
    OS P Q A B := sorry

theorem l9_18 (X Y A B P : Tpoint) (h₁ : Col X Y P) (h₂ : Col A B P) :
    TS X Y A B ↔ (Bet A P B ∧ ¬ Col X Y A ∧ ¬ Col X Y B) := sorry

theorem l9_19 (X Y A B P : Tpoint) (h₁ : Col X Y P) (h₂ : Col A B P) :
    OS X Y A B ↔ (Out P A B ∧ ¬ Col X Y A) := sorry

theorem one_side_not_col123 (A B X Y : Tpoint) (h : OS A B X Y) :
    ¬ Col A B X := sorry

theorem one_side_not_col124 (A B X Y : Tpoint) (h : OS A B X Y) :
    ¬ Col A B Y := sorry

theorem col_two_sides (A B C P Q : Tpoint)
    (hCol : Col A B C) (hAC : A ≠ C) (h : TS A B P Q) : TS A C P Q := sorry

theorem col_one_side (A B C P Q : Tpoint)
    (hCol : Col A B C) (hAC : A ≠ C) (h : OS A B P Q) : OS A C P Q := sorry

theorem out_out_one_side (A B X Y Z : Tpoint)
    (h₁ : OS A B X Y) (h₂ : Out A Y Z) : OS A B X Z := sorry

theorem out_one_side (A B X Y : Tpoint)
    (h₁ : ¬ Col A B X ∨ ¬ Col A B Y) (h₂ : Out A X Y) : OS A B X Y := sorry

theorem bet__ts (A B X Y : Tpoint)
    (hAY : A ≠ Y) (hNCol : ¬ Col A B X) (hBet : Bet X A Y) : TS A B X Y := sorry

theorem bet_ts__ts (A B X Y Z : Tpoint) (h₁ : TS A B X Y) (h₂ : Bet X Y Z) :
    TS A B X Z := sorry

theorem bet_ts__os (A B X Y Z : Tpoint) (h₁ : TS A B X Y) (h₂ : Bet X Y Z) :
    OS A B Y Z := sorry

theorem l9_31 (A X Y Z : Tpoint) (h₁ : OS A X Y Z) (h₂ : OS A Z Y X) :
    TS A Y X Z := sorry

theorem col123__nos (A B P Q : Tpoint) (h : Col P Q A) : ¬ OS P Q A B := sorry

theorem col124__nos (A B P Q : Tpoint) (h : Col P Q B) : ¬ OS P Q A B := sorry

theorem col2_os__os (A B C D X Y : Tpoint)
    (hCD : C ≠ D) (h₁ : Col A B C) (h₂ : Col A B D) (h₃ : OS A B X Y) :
    OS C D X Y := sorry

theorem os_out_os (A B C D C' P : Tpoint)
    (hCol : Col A B P) (h₁ : OS A B C D) (h₂ : Out P C C') :
    OS A B C' D := sorry

theorem ts_ts_os (A B C D : Tpoint) (h₁ : TS A B C D) (h₂ : TS C D A B) :
    OS A C B D := sorry

theorem two_sides_not_col (A B X Y : Tpoint) (h : TS A B X Y) :
    ¬ Col A B X := sorry

theorem col_one_side_out (A B X Y : Tpoint) (hCol : Col A X Y) (h : OS A B X Y) :
    Out A X Y := sorry

theorem col_two_sides_bet (A B X Y : Tpoint)
    (hCol : Col A X Y) (h : TS A B X Y) : Bet X A Y := sorry

theorem os_ts1324__os (A X Y Z : Tpoint)
    (h₁ : OS A X Y Z) (h₂ : TS A Y X Z) : OS A Z X Y := sorry

theorem ts2__ex_bet2 (A B C D : Tpoint) (h₁ : TS A C B D) (h₂ : TS B D A C) :
    ∃ X, Bet A X C ∧ Bet B X D := sorry

theorem out_one_side_1 (A B C D X : Tpoint)
    (hNCol : ¬ Col A B C) (hCol : Col A B X) (hOut : Out X C D) :
    OS A B C D := sorry

theorem out_two_sides_two_sides (A B X Y P PX : Tpoint)
    (hA_PX : A ≠ PX) (hCol : Col A B PX) (hOut : Out PX X P)
    (h : TS A B P Y) : TS A B X Y := sorry

theorem l8_21_bis (A B C X Y : Tpoint)
    (hXY : X ≠ Y) (hNCol : ¬ Col C A B) :
    ∃ P : Tpoint, Cong A P X Y ∧ Perp A B P A ∧ TS A B C P := sorry

theorem ts__ncol (A B X Y : Tpoint) (h : TS A B X Y) :
    ¬ Col A X Y ∨ ¬ Col B X Y := sorry

theorem one_or_two_sides_aux (A B C D X : Tpoint)
    (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B)
    (h₁ : Col A C X) (h₂ : Col B D X) : TS A B C D ∨ OS A B C D := sorry

theorem cop__one_or_two_sides (A B C D : Tpoint)
    (hCop : Coplanar A B C D) (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B) :
    TS A B C D ∨ OS A B C D := sorry

theorem os__coplanar (A B C D : Tpoint) (h : OS A B C D) :
    Coplanar A B C D := sorry

theorem coplanar_trans_1 (P Q R A B : Tpoint)
    (hNCol : ¬ Col P Q R)
    (h₁ : Coplanar P Q R A) (h₂ : Coplanar P Q R B) :
    Coplanar Q R A B := sorry

theorem col_cop__cop (A B C D E : Tpoint)
    (hCop : Coplanar A B C D) (hCD : C ≠ D) (hCol : Col C D E) :
    Coplanar A B C E := sorry

theorem bet_cop__cop (A B C D E : Tpoint)
    (hCop : Coplanar A B C E) (hBet : Bet C D E) : Coplanar A B C D := sorry

theorem col2_cop__cop (A B C D E F : Tpoint)
    (hCop : Coplanar A B C D) (hCD : C ≠ D)
    (h₁ : Col C D E) (h₂ : Col C D F) : Coplanar A B E F := sorry

theorem col_cop2__cop (A B C U V P : Tpoint)
    (hUV : U ≠ V) (h₁ : Coplanar A B C U) (h₂ : Coplanar A B C V)
    (hCol : Col U V P) : Coplanar A B C P := sorry

theorem bet_cop2__cop (A B C U V W : Tpoint)
    (h₁ : Coplanar A B C U) (h₂ : Coplanar A B C W) (hBet : Bet U V W) :
    Coplanar A B C V := sorry

theorem coplanar_pseudo_trans (A B C D P Q R : Tpoint)
    (hNCol : ¬ Col P Q R)
    (h₁ : Coplanar P Q R A) (h₂ : Coplanar P Q R B)
    (h₃ : Coplanar P Q R C) (h₄ : Coplanar P Q R D) :
    Coplanar A B C D := sorry

theorem l9_30 (A B C D E F P X Y Z : Tpoint)
    (hNCopP : ¬ Coplanar A B C P) (hNColDEF : ¬ Col D E F)
    (hCopDEF_P : Coplanar D E F P)
    (h₁ : Coplanar A B C X) (h₂ : Coplanar A B C Y) (h₃ : Coplanar A B C Z)
    (h₄ : Coplanar D E F X) (h₅ : Coplanar D E F Y) (h₆ : Coplanar D E F Z) :
    Col X Y Z := sorry

theorem cop_per2__col (A X Y Z : Tpoint)
    (hCop : Coplanar A X Y Z) (hAZ : A ≠ Z)
    (h₁ : Per X Z A) (h₂ : Per Y Z A) : Col X Y Z := sorry

theorem cop_perp2__col (X Y Z A B : Tpoint)
    (hCop : Coplanar A B Y Z) (h₁ : Perp X Y A B) (h₂ : Perp X Z A B) :
    Col X Y Z := sorry

theorem two_sides_dec (A B C D : Tpoint) : TS A B C D ∨ ¬ TS A B C D := sorry

theorem cop_nts__os (A B C D : Tpoint)
    (hCop : Coplanar A B C D) (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B)
    (hNTS : ¬ TS A B C D) : OS A B C D := sorry

theorem cop_nos__ts (A B C D : Tpoint)
    (hCop : Coplanar A B C D) (hNC1 : ¬ Col C A B) (hNC2 : ¬ Col D A B)
    (hNOS : ¬ OS A B C D) : TS A B C D := sorry

theorem one_side_dec (A B C D : Tpoint) : OS A B C D ∨ ¬ OS A B C D := sorry

theorem cop_dec (A B C D : Tpoint) : Coplanar A B C D ∨ ¬ Coplanar A B C D := sorry

theorem ex_diff_cop (A B C D : Tpoint) :
    ∃ E, Coplanar A B C E ∧ D ≠ E := sorry

theorem ex_ncol_cop (A B C D E : Tpoint) (hDE : D ≠ E) :
    ∃ F, Coplanar A B C F ∧ ¬ Col D E F := sorry

theorem ex_ncol_cop2 (A B C D : Tpoint) :
    ∃ E F, Coplanar A B C E ∧ Coplanar A B C F ∧ ¬ Col D E F := sorry

theorem col2_cop2__eq (A B C U V P Q : Tpoint)
    (hNCop : ¬ Coplanar A B C U) (hUV : U ≠ V)
    (h₁ : Coplanar A B C P) (h₂ : Coplanar A B C Q)
    (h₃ : Col U V P) (h₄ : Col U V Q) : P = Q := sorry

theorem cong3_cop2__col (A B C P Q : Tpoint)
    (h₁ : Coplanar A B C P) (h₂ : Coplanar A B C Q) (hPQ : P ≠ Q)
    (h₃ : Cong A P A Q) (h₄ : Cong B P B Q) (h₅ : Cong C P C Q) :
    Col A B C := sorry

theorem l9_38 (A B C P Q : Tpoint) (h : TSP A B C P Q) : TSP A B C Q P := sorry

theorem l9_39 (A B C D P Q R : Tpoint)
    (h₁ : TSP A B C P R) (hCop : Coplanar A B C D) (hOut : Out D P Q) :
    TSP A B C Q R := sorry

theorem l9_41_1 (A B C P Q R : Tpoint)
    (h₁ : TSP A B C P R) (h₂ : TSP A B C Q R) : OSP A B C P Q := sorry

theorem l9_41_2 (A B C P Q R : Tpoint)
    (h₁ : TSP A B C P R) (h₂ : OSP A B C P Q) : TSP A B C Q R := sorry

theorem tsp_exists (A B C P : Tpoint) (hNCop : ¬ Coplanar A B C P) :
    ∃ Q, TSP A B C P Q := sorry

theorem osp_reflexivity (A B C P : Tpoint) (hNCop : ¬ Coplanar A B C P) :
    OSP A B C P P := sorry

theorem osp_symmetry (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    OSP A B C Q P := sorry

theorem osp_transitivity (A B C P Q R : Tpoint)
    (h₁ : OSP A B C P Q) (h₂ : OSP A B C Q R) : OSP A B C P R := sorry

theorem cop3_tsp__tsp (A B C D E F P Q : Tpoint)
    (hNCol : ¬ Col D E F)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E) (h₃ : Coplanar A B C F)
    (h₄ : TSP A B C P Q) : TSP D E F P Q := sorry

theorem cop3_osp__osp (A B C D E F P Q : Tpoint)
    (hNCol : ¬ Col D E F)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E) (h₃ : Coplanar A B C F)
    (h₄ : OSP A B C P Q) : OSP D E F P Q := sorry

theorem ncop_distincts (A B C D : Tpoint) (h : ¬ Coplanar A B C D) :
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D := sorry

theorem tsp_distincts (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
    A ≠ P ∧ B ≠ P ∧ C ≠ P ∧
    A ≠ Q ∧ B ≠ Q ∧ C ≠ Q ∧ P ≠ Q := sorry

theorem osp_distincts (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
    A ≠ P ∧ B ≠ P ∧ C ≠ P ∧
    A ≠ Q ∧ B ≠ Q ∧ C ≠ Q := sorry

theorem tsp__ncop1 (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    ¬ Coplanar A B C P := sorry

theorem tsp__ncop2 (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    ¬ Coplanar A B C Q := sorry

theorem osp__ncop1 (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    ¬ Coplanar A B C P := sorry

theorem osp__ncop2 (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    ¬ Coplanar A B C Q := sorry

theorem tsp__nosp (A B C P Q : Tpoint) (h : TSP A B C P Q) :
    ¬ OSP A B C P Q := sorry

theorem osp__ntsp (A B C P Q : Tpoint) (h : OSP A B C P Q) :
    ¬ TSP A B C P Q := sorry

theorem osp_bet__osp (A B C P Q R : Tpoint)
    (h₁ : OSP A B C P R) (h₂ : Bet P Q R) : OSP A B C P Q := sorry

theorem l9_18_3 (A B C X Y P : Tpoint)
    (hCop : Coplanar A B C P) (hCol : Col X Y P) :
    TSP A B C X Y ↔ Bet X P Y ∧ ¬ Coplanar A B C X ∧ ¬ Coplanar A B C Y := sorry

theorem bet_cop__tsp (A B C X Y P : Tpoint)
    (hNCop : ¬ Coplanar A B C X) (hPY : P ≠ Y)
    (hCop : Coplanar A B C P) (hBet : Bet X P Y) : TSP A B C X Y := sorry

theorem cop_out__osp (A B C X Y P : Tpoint)
    (hNCop : ¬ Coplanar A B C X) (hCop : Coplanar A B C P)
    (hOut : Out P X Y) : OSP A B C X Y := sorry

theorem l9_19_3 (A B C X Y P : Tpoint)
    (hCop : Coplanar A B C P) (hCol : Col X Y P) :
    OSP A B C X Y ↔ Out P X Y ∧ ¬ Coplanar A B C X := sorry

theorem cop2_ts__tsp (A B C D E X Y : Tpoint)
    (hNCop : ¬ Coplanar A B C X)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : TS D E X Y) : TSP A B C X Y := sorry

theorem cop2_os__osp (A B C D E X Y : Tpoint)
    (hNCop : ¬ Coplanar A B C X)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : OS D E X Y) : OSP A B C X Y := sorry

theorem cop3_tsp__ts (A B C D E X Y : Tpoint)
    (hDE : D ≠ E)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : Coplanar D E X Y) (h₄ : TSP A B C X Y) : TS D E X Y := sorry

theorem cop3_osp__os (A B C D E X Y : Tpoint)
    (hDE : D ≠ E)
    (h₁ : Coplanar A B C D) (h₂ : Coplanar A B C E)
    (h₃ : Coplanar D E X Y) (h₄ : OSP A B C X Y) : OS D E X Y := sorry

theorem cop_tsp__ex_cop2 (A B C D E P : Tpoint)
    (hCop : Coplanar A B C P) (h : TSP A B C D E) :
    ∃ Q, Coplanar A B C Q ∧ Coplanar D E P Q ∧ P ≠ Q := sorry

theorem cop_osp__ex_cop2 (A B C D E P : Tpoint)
    (hCop : Coplanar A B C P) (h : OSP A B C D E) :
    ∃ Q, Coplanar A B C Q ∧ Coplanar D E P Q ∧ P ≠ Q := sorry

theorem sac__coplanar (A B C D : Tpoint) (h : Saccheri A B C D) :
    Coplanar A B C D := sorry

end T9

end GeocoqTranslate.Tarski
