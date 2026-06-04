-- Translated from theories/Axioms/rocq_demo.v via rocq-mcp + lean-lsp-mcp.

theorem add_0_r : ∀ n : Nat, n + 0 = n := by
  intro n; rfl

theorem add_comm : ∀ n m : Nat, n + m = m + n := by
  intro n m
  induction n with
  | zero => simp
  | succ k ih => rw [Nat.succ_add, ih, ← Nat.add_succ]

theorem length_app : ∀ (A : Type) (l l' : List A),
    (l ++ l').length = l.length + l'.length := by
  intro A l l'
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.cons_append, List.length_cons, ih, Nat.succ_add]

theorem de_morgan : ∀ P Q : Prop, ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  intro P Q
  constructor
  · intro h
    exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩
  · intro ⟨hnp, hnq⟩ h
    cases h with
    | inl hp => exact hnp hp
    | inr hq => exact hnq hq

theorem exists_not_all : ∀ P : Nat → Prop,
    (∃ n : Nat, P n) → ¬ (∀ n : Nat, ¬ P n) := by
  intro P ⟨n, hn⟩ hall
  exact hall n hn
