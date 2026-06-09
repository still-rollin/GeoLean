/-
Translated from theories/Elements/OriginalProofs/proposition_02.v.

Euclid, Elements Book I, Proposition 2:
  "To place at a given point (as an extremity) a straight line equal to
  a given straight line."

Given A ≠ B and B ≠ C, there exists a point X with `Cong A X B C`.

Proof structure (mirroring Euclid):
  1. Build the equilateral triangle ABD via `proposition_01`.
  2. Circle J = circle(B, BC). Line DB meets J at G past B; so `Cong B G B C`.
  3. Circle R = circle(D, DG). Line DA meets R at L past A; so `Cong D L D G`.
  4. Apply `lemma_differenceofparts` to subtract the equal segments DB = DA
     from DG and DL, yielding `Cong B G A L`. Chain with `Cong B G B C` to
     obtain `Cong A L B C`. Witness: L.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.euclidean_defs
import GeocoqTranslate.Elements.OriginalProofs.proposition_01
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruenceflip
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_NCdistinct
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_betweennotequal
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_differenceofparts

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem proposition_02 (A B C : Point) (hAB : A ≠ B) (hBC : B ≠ C) :
    ∃ X, Cong A X B C := by
  -- Phase 1: equilateral triangle ABD via proposition_01.
  obtain ⟨D, hEqui, hTri⟩ := proposition_01 A B hAB
  have hCong_AB_BD : Cong A B B D := hEqui.1
  have hCong_BD_DA : Cong B D D A := hEqui.2
  have hNCol : nCol A B D := hTri
  -- Distinctness facts from the triangle.
  have hDB : D ≠ B := (lemma_NCdistinct A B D hNCol).2.2.2.2.1
  have hDA : D ≠ A := (lemma_NCdistinct A B D hNCol).2.2.2.2.2

  -- Phase 2: circle J centred at B with radius BC; line DB meets J at G.
  obtain ⟨J, hCI_J⟩ := postulate_Euclid3 B C hBC
  have hInCirc_B_J : InCirc B J := by
    show ∃ X Y U V W : Point,
      CI J U V W ∧ (B = U ∨ (BetS U Y X ∧ Cong U X V W ∧ Cong U B U Y))
    exact ⟨B, B, B, B, C, hCI_J, Or.inl rfl⟩
  obtain ⟨P, G, _hCol_DBP, hBetS_DBG, _hOnCirc_P_J, hOnCirc_G_J, _hBetS_PBG⟩ :=
    postulate_line_circle D B B J B C hCI_J hInCirc_B_J hDB
  have hCong_BG_BC : Cong B G B C :=
    axiom_circle_center_radius B B C J G hCI_J hOnCirc_G_J
  have hDG : D ≠ G := (lemma_betweennotequal D B G hBetS_DBG).2.2

  -- Phase 3: circle R centred at D with radius DG; line DA meets R at L.
  obtain ⟨R, hCI_R⟩ := postulate_Euclid3 D G hDG
  -- Set up Cong D A D B for the InCirc witness.
  have hCong_DA_BD : Cong D A B D := lemma_congruencesymmetric D B D A hCong_BD_DA
  have hCong_DA_DB : Cong D A D B := (lemma_congruenceflip D A B D hCong_DA_BD).2.2
  have hCong_DG_DG : Cong D G D G := cn_congruencereflexive D G
  have hInCirc_A_R : InCirc A R := by
    show ∃ X Y U V W : Point,
      CI R U V W ∧ (A = U ∨ (BetS U Y X ∧ Cong U X V W ∧ Cong U A U Y))
    exact ⟨G, B, D, D, G, hCI_R, Or.inr ⟨hBetS_DBG, hCong_DG_DG, hCong_DA_DB⟩⟩
  obtain ⟨_Q, L, _hCol_DAQ, hBetS_DAL, _hOnCirc_Q_R, hOnCirc_L_R, _hBetS_QAL⟩ :=
    postulate_line_circle D A D R D G hCI_R hInCirc_A_R hDA
  have hCong_DL_DG : Cong D L D G :=
    axiom_circle_center_radius D D G R L hCI_R hOnCirc_L_R

  -- Phase 4: subtract DA from DL and DB from DG via lemma_differenceofparts.
  have hCong_DB_DA : Cong D B D A := lemma_congruencesymmetric D D A B hCong_DA_DB
  have hCong_DG_DL : Cong D G D L := lemma_congruencesymmetric D D L G hCong_DL_DG
  have hCong_BG_AL : Cong B G A L :=
    lemma_differenceofparts D B G D A L hCong_DB_DA hCong_DG_DL hBetS_DBG hBetS_DAL
  have hCong_AL_BC : Cong A L B C :=
    cn_congruencetransitive A L B C B G hCong_BG_AL hCong_BG_BC

  exact ⟨L, hCong_AL_BC⟩

end GeocoqTranslate.Elements
