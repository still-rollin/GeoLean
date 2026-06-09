/-
Translated from theories/Elements/OriginalProofs/lemma_differenceofparts.v.

  Cong A B a b → Cong A C a c → BetS A B C → BetS a b c → Cong B C b c

Case split on `B = A`:
  * If `B = A`, then `Cong A A a b` forces `a = b` (via `axiom_nocollapse`),
    and the goal collapses to the given `Cong A C a c`.
  * Otherwise, build local extensions `E` past `A` on line `CA`, and the
    matching `e` on `ca`, then chain `axiom_5_line` with `cn_sumofparts`
    to get `Cong C B c b`, and flip via `lemma_doublereverse`.
-/

import GeocoqTranslate.Euclidean.Axioms
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencesymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_congruencetransitive
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_inequalitysymmetric
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_localextension
import GeocoqTranslate.Elements.OriginalProofs.Lemmas.lemma_doublereverse

namespace GeocoqTranslate.Elements

open euclidean_neutral_basis euclidean_neutral euclidean_neutral_ruler_compass

variable {Point : Type} [euclidean_neutral_ruler_compass Point]

theorem lemma_differenceofparts (A B C a b c : Point)
    (h1 : Cong A B a b) (h2 : Cong A C a c)
    (h3 : BetS A B C) (h4 : BetS a b c) :
    Cong B C b c := by
  -- Case split via `cn_stability` to avoid relying on Mathlib's `by_cases`.
  by_cases hBA : B = A
  · subst hBA
    have hab : a = b := by
      apply cn_stability
      intro hab_ne
      exact axiom_nocollapse a b B B hab_ne
        (lemma_congruencesymmetric a B B b h1) rfl
    exact hab ▸ h2
  · -- B ≠ A: extend past A on both lines, then chain axiom_5_line.
    have hBA' : B ≠ A := hBA
    have hCA : C ≠ A := by
      intro hCAeq
      rw [hCAeq] at h3
      exact axiom_betweennessidentity A B h3
    have hAC : A ≠ C := fun h => hCA h.symm
    obtain ⟨E, hBetS_CAE, hCong_AE_AC⟩ :=
      lemma_localextension C A C hCA hAC
    have hac : a ≠ c := axiom_nocollapse A C a c hAC h2
    have hca : c ≠ a := fun h => hac h.symm
    obtain ⟨e, hBetS_cae, hCong_ae_ac⟩ :=
      lemma_localextension c a c hca hac
    have h_EA_AE : Cong E A A E := cn_equalityreverse E A
    have h_EA_AC : Cong E A A C :=
      lemma_congruencetransitive E A A E A C h_EA_AE hCong_AE_AC
    have h_EA_ac : Cong E A a c :=
      lemma_congruencetransitive E A A C a c h_EA_AC h2
    have h_ea_ae : Cong e a a e := cn_equalityreverse e a
    have h_ea_ac : Cong e a a c :=
      lemma_congruencetransitive e a a e a c h_ea_ae hCong_ae_ac
    have h_ac_ea : Cong a c e a :=
      lemma_congruencesymmetric a e a c h_ea_ac
    have h_EA_ea : Cong E A e a :=
      lemma_congruencetransitive E A a c e a h_EA_ac h_ac_ea
    have h_BetS_EAC : BetS E A C := axiom_betweennesssymmetry C A E hBetS_CAE
    have h_BetS_eac : BetS e a c := axiom_betweennesssymmetry c a e hBetS_cae
    have h_EC_ec : Cong E C e c :=
      cn_sumofparts E A C e a c h_EA_ea h2 h_BetS_EAC h_BetS_eac
    have h_BetS_EAB : BetS E A B :=
      axiom_innertransitivity E A B C h_BetS_EAC h3
    have h_BetS_eab : BetS e a b :=
      axiom_innertransitivity e a b c h_BetS_eac h4
    have h_CB_cb : Cong C B c b :=
      axiom_5_line E A B C e a b c h1 h_EC_ec h2 h_BetS_EAB h_BetS_eab h_EA_ea
    exact (lemma_doublereverse C B c b h_CB_cb).2

end GeocoqTranslate.Elements
