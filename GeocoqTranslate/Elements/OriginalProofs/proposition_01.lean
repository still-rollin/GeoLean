/-
Translated from theories/Elements/OriginalProofs/proposition_01.v.

Euclid, Elements Book I, Proposition 1:
  "On a given finite straight line, to construct an equilateral triangle."

Given two distinct points A and B, there exists a point C such that
ABC is an equilateral triangle.

Proof structure (three phases, mirroring Euclid):
  1. Build the two circles centered at A and B (both with radius AB) and
     take their intersection point C via `postulate_circle_circle`.
  2. From the circle-radius axiom, derive Cong A B B C and Cong B C C A
     and combine them into `equilateral A B C`.
  3. Show C is not on the line AB (via `lemma_partnotequalwhole`),
     yielding the non-degeneracy condition `Triangle A B C`.

-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.euclidean_defs
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencetransitive
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruenceflip
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_inequalitysymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_localextension
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_partnotequalwhole

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem proposition_01 (A B : Point) (hAB : A ≠ B) :
    ∃ C, equilateral A B C ∧ Triangle A B C := by
  -- Phase 1: build the two circles and their intersection point C
  obtain ⟨J, hCI_J⟩ := postulate_Euclid3 A B hAB
  have hBA : B ≠ A := lemma_inequalitysymmetric A B hAB
  obtain ⟨K, hCI_K⟩ := postulate_Euclid3 B A hBA
  obtain ⟨D, hBet_BAD, hCong_AD_AB⟩ :=
    lemma_localextension B A B hBA hAB
  have hInCirc_B_K : InCirc B K := by
    show ∃ X Y U V W : Point,
      CI K U V W ∧ (B = U ∨ (BetS U Y X ∧ Cong U X V W ∧ Cong U B U Y))
    exact ⟨B, B, B, B, A, hCI_K, Or.inl rfl⟩
  have hOutCirc_D_K : OutCirc D K := by
    show ∃ X U V W : Point, CI K U V W ∧ BetS U X D ∧ Cong U X V W
    exact ⟨A, B, B, A, hCI_K, hBet_BAD, cn_congruencereflexive B A⟩
  have hOnCirc_B_J : OnCirc B J := by
    show ∃ X Y U : Point, CI J U X Y ∧ Cong U B X Y
    exact ⟨A, B, A, hCI_J, cn_congruencereflexive A B⟩
  have hOnCirc_D_J : OnCirc D J := by
    show ∃ X Y U : Point, CI J U X Y ∧ Cong U D X Y
    exact ⟨A, B, A, hCI_J, hCong_AD_AB⟩
  obtain ⟨C, hOnC_K, hOnC_J⟩ :=
    postulate_circle_circle B A A B K J B D B A
      hCI_K hInCirc_B_K hOutCirc_D_K hCI_J hOnCirc_B_J hOnCirc_D_J

  -- Phase 2: derive equilateral A B C from circle-radius congruences
  have hCong_AC_AB : Cong A C A B := axiom_circle_center_radius A A B J C hCI_J hOnC_J
  have hCong_AB_AC : Cong A B A C := lemma_congruencesymmetric A A C B hCong_AC_AB
  have hCong_BC_BA : Cong B C B A := axiom_circle_center_radius B B A K C hCI_K hOnC_K
  have hCong_BC_AB : Cong B C A B := (lemma_congruenceflip B C B A hCong_BC_BA).2.2
  have hCong_BC_AC : Cong B C A C :=
    lemma_congruencetransitive B C A B A C hCong_BC_AB hCong_AB_AC
  have hCong_AB_BC : Cong A B B C := lemma_congruencesymmetric A B C B hCong_BC_AB
  have hCong_AC_CA : Cong A C C A := cn_equalityreverse A C
  have hCong_BC_CA : Cong B C C A :=
    lemma_congruencetransitive B C A C C A hCong_BC_AC hCong_AC_CA
  have hEqui : equilateral A B C := by
    show Cong A B B C ∧ Cong B C C A
    exact ⟨hCong_AB_BC, hCong_BC_CA⟩

  -- Phase 3: non-collinearity via partnotequalwhole on each BetS arrangement
  have hBC : B ≠ C := axiom_nocollapse A B B C hAB hCong_AB_BC
  have hCA : C ≠ A := axiom_nocollapse B C C A hBC hCong_BC_CA
  have hNotBetSAcb : ¬ BetS A C B :=
    fun hBetS => lemma_partnotequalwhole A C B hBetS hCong_AC_AB
  have hNotBetSAbc : ¬ BetS A B C :=
    fun hBetS => lemma_partnotequalwhole A B C hBetS hCong_AB_AC
  have hCong_BA_BC : Cong B A B C := (lemma_congruenceflip A B B C hCong_AB_BC).2.1
  have hNotBetSBac : ¬ BetS B A C :=
    fun hBetS => lemma_partnotequalwhole B A C hBetS hCong_BA_BC
  have hTriangle : Triangle A B C := by
    show A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ ¬ BetS A B C ∧ ¬ BetS A C B ∧ ¬ BetS B A C
    exact ⟨hAB, fun h => hCA h.symm, hBC,
           hNotBetSAbc, hNotBetSAcb, hNotBetSBac⟩

  exact ⟨C, hEqui, hTriangle⟩

end GeocoqTranslate.Elements
