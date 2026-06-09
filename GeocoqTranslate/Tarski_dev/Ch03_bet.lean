/-
Translated from theories/Main/Tarski_dev/Ch03_bet.v.

Statement-only translation (Phase 0 of the GeoCoq → Lean port).
All proofs are `sorry`; signatures match the Rocq originals.

Sections T2_1 (Tarski neutral) and T2_2/T2_3/T2_4 (with decidable point
equality). Two Beeson sections use a hypothesis `Bet_stability` /
`Cong_stability` rather than the decidable-equality instance.
-/

import Aesop
import GeocoqTranslate.Tarski.Axioms
import GeocoqTranslate.Tarski.Definitions
import GeocoqTranslate.Tarski_dev.Ch02_cong

namespace GeocoqTranslate.Tarski

open Tarski_neutral_dimensionless
open Tarski_neutral_dimensionless_with_decidable_point_equality

/-! ## T2_1: betweenness basics (neutral) -/

section T2_1
variable {Tpoint : Type} [Tarski_neutral_dimensionless Tpoint]

@[aesop safe]
theorem bet_col (A B C : Tpoint) (h : Bet A B C) : Col A B C :=
  .inl h

@[aesop safe]
theorem between_trivial (A B : Tpoint) : Bet A B B := by
  obtain ⟨x, hBet, hCong⟩ := segment_construction A B B B
  have hBx : B = x := cong_identity B x B hCong
  rwa [← hBx] at hBet

@[aesop safe forward]
theorem between_symmetry (A B C : Tpoint) (h : Bet A B C) : Bet C B A := by
  have hBCC : Bet B C C := between_trivial B C
  obtain ⟨x, hBxB, hCxA⟩ := inner_pasch A B C B C h hBCC
  have hBx : B = x := between_identity B x hBxB
  rwa [← hBx] at hCxA

theorem Bet_cases (A B C : Tpoint) (h : Bet A B C ∨ Bet C B A) : Bet A B C := by
  rcases h with h | h
  · exact h
  · exact between_symmetry _ _ _ h

theorem Bet_perm (A B C : Tpoint) (h : Bet A B C) : Bet A B C ∧ Bet C B A :=
  ⟨h, between_symmetry _ _ _ h⟩

@[aesop safe]
theorem between_trivial2 (A B : Tpoint) : Bet A A B :=
  between_symmetry B A A (between_trivial B A)

theorem between_equality (A B C : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet B A C) : A = B := by
  obtain ⟨x, hBxB, hAxA⟩ := inner_pasch A B C B A h₁ h₂
  have hBx : B = x := between_identity B x hBxB
  have hAx : A = x := between_identity A x hAxA
  exact hAx.trans hBx.symm

theorem between_equality_2 (A B C : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C B) : B = C :=
  between_equality B C A (between_symmetry _ _ _ h₂) (between_symmetry _ _ _ h₁)

theorem between_exchange3 (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C D) : Bet B C D := by
  have hsC : Bet D C A := between_symmetry _ _ _ h₂
  have hsB : Bet C B A := between_symmetry _ _ _ h₁
  obtain ⟨x, hCxC, hBxD⟩ := inner_pasch D C A C B hsC hsB
  have hCx : C = x := between_identity C x hCxC
  rwa [← hCx] at hBxD

theorem bet_neq12__neq (A B C : Tpoint) (h : Bet A B C) (hAB : A ≠ B) : A ≠ C := by
  intro hAC
  rw [← hAC] at h
  exact hAB (between_identity A B h)

theorem bet_neq21__neq (A B C : Tpoint) (h : Bet A B C) (hBA : B ≠ A) : A ≠ C :=
  bet_neq12__neq A B C h (fun hAB => hBA hAB.symm)

theorem bet_neq23__neq (A B C : Tpoint) (h : Bet A B C) (hBC : B ≠ C) : A ≠ C := by
  intro hAC
  rw [hAC] at h
  exact hBC (between_identity C B h).symm

theorem bet_neq32__neq (A B C : Tpoint) (h : Bet A B C) (hCB : C ≠ B) : A ≠ C :=
  bet_neq23__neq A B C h (fun hBC => hCB hBC.symm)

theorem not_bet_distincts (A B C : Tpoint) (h : ¬ Bet A B C) :
    A ≠ B ∧ B ≠ C := by
  refine ⟨?_, ?_⟩
  · intro hAB; subst hAB; exact h (between_trivial2 A C)
  · intro hBC; subst hBC; exact h (between_trivial A B)

end T2_1

/-! ## T2_2: inner / outer transitivity (decidable equality) -/

section T2_2
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem between_inner_transitivity (A B C D : Tpoint)
    (h₁ : Bet A B D) (h₂ : Bet B C D) : Bet A B C := by
  obtain ⟨x, hBxB, hCxA⟩ := inner_pasch A B D B C h₁ h₂
  have hBx : B = x := between_identity B x hBxB
  rw [← hBx] at hCxA
  exact between_symmetry _ _ _ hCxA

theorem outer_transitivity_between2 (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet B C D) (hBC : B ≠ C) : Bet A C D := by
  obtain ⟨x, hACx, hCxCD⟩ := segment_construction A C C D
  have hBCx : Bet B C x := between_exchange3 _ _ _ _ h₁ hACx
  have hxD : x = D :=
    construction_uniqueness B C C D x D hBC hBCx hCxCD h₂ (cong_reflexivity C D)
  rwa [← hxD]

end T2_2

/-! ## T2_3: exchange / outer transitivity -/

section T2_3
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem between_exchange2 (A B C D : Tpoint)
    (h₁ : Bet A B D) (h₂ : Bet B C D) : Bet A C D := by
  rcases point_equality_decidability B C with hBC | hBC
  · rw [← hBC]; exact h₁
  · have hABC : Bet A B C := between_inner_transitivity A B C D h₁ h₂
    exact outer_transitivity_between2 A B C D hABC h₂ hBC

theorem outer_transitivity_between (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet B C D) (hBC : B ≠ C) : Bet A B D :=
  between_symmetry _ _ _
    (outer_transitivity_between2 D C B A
      (between_symmetry _ _ _ h₂) (between_symmetry _ _ _ h₁)
      (fun hCB => hBC hCB.symm))

theorem between_exchange4 (A B C D : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A C D) : Bet A B D :=
  between_symmetry _ _ _
    (between_exchange2 D C B A (between_symmetry _ _ _ h₂) (between_symmetry _ _ _ h₁))

end T2_3

/-! ## T2_4: four-point betweenness, existence lemmas -/

section T2_4
variable {Tpoint : Type}
    [Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint]

theorem l3_9_4 (A₁ A₂ A₃ A₄ : Tpoint) (h : Bet_4 A₁ A₂ A₃ A₄) :
    Bet_4 A₄ A₃ A₂ A₁ := by
  unfold Bet_4 at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨between_symmetry _ _ _ h2, between_symmetry _ _ _ h1,
         between_symmetry _ _ _ h4, between_symmetry _ _ _ h3⟩

theorem l3_17 (A B C A' B' P : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C) (h₃ : Bet A P A') :
    ∃ Q, Bet P Q C ∧ Bet B Q B' := by
  -- First inner_pasch: from `Bet C B' A'` and `Bet A P A'` get
  -- `∃ x, Bet B' x A ∧ Bet P x C`.
  obtain ⟨x, hB'xA, hPxC⟩ :=
    inner_pasch C A A' B' P (between_symmetry _ _ _ h₂) h₃
  -- Second inner_pasch: from `Bet B' x A` and `Bet C B A` get
  -- `∃ y, Bet x y C ∧ Bet B y B'`.
  obtain ⟨y, hxyC, hByB'⟩ :=
    inner_pasch B' C A x B hB'xA (between_symmetry _ _ _ h₁)
  -- Combine: `Bet P y C` follows from `Bet P x C` and `Bet x y C`.
  exact ⟨y, between_exchange2 _ _ _ _ hPxC hxyC, hByB'⟩

theorem lower_dim_ex :
    ∃ A B C : Tpoint, ¬ (Bet A B C ∨ Bet B C A ∨ Bet C A B) :=
  ⟨PA, PB, PC, lower_dim⟩

theorem two_distinct_points : ∃ X Y : Tpoint, X ≠ Y := by
  obtain ⟨A, B, C, h⟩ := lower_dim_ex (Tpoint := Tpoint)
  refine ⟨A, B, ?_⟩
  intro hAB
  subst hAB
  exact h (.inr (.inr (between_trivial C A)))

theorem point_construction_different (A B : Tpoint) :
    ∃ C, Bet A B C ∧ B ≠ C := by
  obtain ⟨x, y, hxy⟩ := two_distinct_points (Tpoint := Tpoint)
  obtain ⟨F, hABF, hCong⟩ := segment_construction A B x y
  refine ⟨F, hABF, ?_⟩
  intro hBF
  apply hxy
  rw [← hBF] at hCong
  exact cong_identity x y B (cong_symmetry _ _ _ _ hCong)

theorem another_point (A : Tpoint) : ∃ B, A ≠ B := by
  obtain ⟨B, _, hAB⟩ := point_construction_different A A
  exact ⟨B, hAB⟩

end T2_4

/-! ## Beeson_1: `l2_11` via `Cong_stability` (no eq-decidability) -/

section Beeson_1
variable {Tpoint : Type} [Tarski_neutral_dimensionless Tpoint]

theorem l2_11_b
    (Cong_stability : ∀ A B C D : Tpoint, ¬ ¬ Cong A B C D → Cong A B C D)
    (A B C A' B' C' : Tpoint)
    (h₁ : Bet A B C) (h₂ : Bet A' B' C')
    (h₃ : Cong A B A' B') (h₄ : Cong B C B' C') : Cong A C A' C' := by
  apply Cong_stability
  intro hNC
  have hAB : A ≠ B := by
    intro hEq
    subst hEq
    have hA'B' : A' = B' :=
      cong_identity A' B' A (cong_symmetry _ _ _ _ h₃)
    subst hA'B'
    exact hNC h₄
  have hCA : Cong C A C' A' :=
    five_segment A A' B B' C C' A A' h₃ h₄
      (cong_trivial_identity A A')
      (cong_commutativity _ _ _ _ h₃) h₁ h₂ hAB
  exact hNC (cong_commutativity _ _ _ _ hCA)

theorem cong_dec_eq_dec_b
    (Cong_stability : ∀ A B C D : Tpoint, ¬ ¬ Cong A B C D → Cong A B C D)
    (A B : Tpoint) (h : ¬ A ≠ B) : A = B := by
  apply cong_identity A B A
  apply Cong_stability
  intro hNCong
  apply h
  intro hEq
  subst hEq
  exact hNCong (cong_pseudo_reflexivity A A)

end Beeson_1

/-! ## Beeson_2: distinctness via `Bet_stability`, plus `BetSEq` -/

section Beeson_2
variable {Tpoint : Type} [Tarski_neutral_dimensionless Tpoint]

theorem bet_dec_eq_dec_b
    (Bet_stability : ∀ A B C : Tpoint, ¬ ¬ Bet A B C → Bet A B C)
    (A B : Tpoint) (h : ¬ A ≠ B) : A = B := by
  apply between_identity A B
  apply Bet_stability
  intro hNBet
  apply h
  intro hEq
  subst hEq
  exact hNBet (between_trivial A A)

theorem BetSEq (A B C : Tpoint) :
    BetS A B C ↔ Bet A B C ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C := Iff.rfl

end Beeson_2

end GeocoqTranslate.Tarski
