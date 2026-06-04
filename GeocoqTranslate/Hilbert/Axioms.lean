/-
Translated from theories/Axioms/hilbert_axioms.v.

Two-class split: structural primitives in `Hilbert_neutral_basis`,
derived predicates as plain `def`s in the surrounding namespace, axioms
in `Hilbert_neutral_dimensionless` extending the basis. This mirrors
Coq's `Definition` semantics — fixed and transparent. See
`Euclidean/Axioms.lean` for the discussion of why the in-class
default-valued-field form was rejected.

Hilbert's axiom system, in six classes:
  1. Hilbert_neutral_basis            -- structural (split out for derived defs)
  2. Hilbert_neutral_dimensionless    -- the main neutral axioms
  3. Hilbert_neutral_2D               -- 2D variant of Pasch
  4. Hilbert_neutral_3D               -- plane intersection + 3D lower-dim
  5. Hilbert_euclidean                -- parallels (uniqueness)
  6. Hilbert_euclidean_ID             -- adds intersection decidability
-/

/-! ## Neutral basis: primitives only -/

/-- Structural primitives of Hilbert neutral geometry. -/
class Hilbert_neutral_basis (Point : Type) where
  Line : Type
  Plane : Type
  EqL : Line → Line → Prop
  EqP : Plane → Plane → Prop
  IncidL : Point → Line → Prop
  IncidP : Point → Plane → Prop
  BetH : Point → Point → Point → Prop
  CongH : Point → Point → Point → Point → Prop
  CongaH : Point → Point → Point → Point → Point → Point → Prop
  PP : Point
  PQ : Point
  PR : Point

namespace Hilbert_neutral_basis

variable {Point : Type} [self : Hilbert_neutral_basis Point]

def ColH (A B C : Point) : Prop :=
  ∃ l : self.Line, self.IncidL A l ∧ self.IncidL B l ∧ self.IncidL C l

def IncidLP (l : self.Line) (p : self.Plane) : Prop :=
  ∀ A : Point, self.IncidL A l → self.IncidP A p

def cut (l : self.Line) (A B : Point) : Prop :=
  ¬ self.IncidL A l ∧ ¬ self.IncidL B l ∧
  ∃ I : Point, self.IncidL I l ∧ self.BetH A I B

def outH (P A B : Point) : Prop :=
  self.BetH P A B ∨ self.BetH P B A ∨ (P ≠ A ∧ A = B)

def disjoint (A B C D : Point) : Prop :=
  ¬ ∃ P : Point, self.BetH A P B ∧ self.BetH C P D

def same_side (A B : Point) (l : self.Line) : Prop :=
  ∃ P : Point, cut l A P ∧ cut l B P

def same_side' (A B X Y : Point) : Prop :=
  X ≠ Y ∧ ∀ l : self.Line, self.IncidL X l → self.IncidL Y l → same_side A B l

end Hilbert_neutral_basis

/-! ## Hilbert neutral (dimensionless) axioms -/

class Hilbert_neutral_dimensionless (Point : Type)
    extends Hilbert_neutral_basis Point where
  EqL_Equiv : Equivalence EqL
  EqP_Equiv : Equivalence EqP
  IncidL_morphism :
    ∀ (P : Point) (l m : Line), IncidL P l → EqL l m → IncidL P m
  IncidL_dec : ∀ (P : Point) (l : Line), IncidL P l ∨ ¬ IncidL P l
  IncidP_morphism :
    ∀ (M : Point) (p q : Plane), IncidP M p → EqP p q → IncidP M q
  IncidP_dec : ∀ (M : Point) (p : Plane), IncidP M p ∨ ¬ IncidP M p
  eq_dec_pointsH : ∀ A B : Point, A = B ∨ ¬ A = B
  -- Group I Incidence
  line_existence :
    ∀ A B : Point, A ≠ B → ∃ l : Line, IncidL A l ∧ IncidL B l
  line_uniqueness :
    ∀ (A B : Point) (l m : Line),
      A ≠ B →
      IncidL A l → IncidL B l → IncidL A m → IncidL B m →
      EqL l m
  two_points_on_line :
    ∀ l : Line, Σ A : Point, { B : Point // IncidL B l ∧ IncidL A l ∧ A ≠ B }
  lower_dim_2 :
    PP ≠ PQ ∧ PQ ≠ PR ∧ PP ≠ PR ∧ ¬ Hilbert_neutral_basis.ColH PP PQ PR
  plane_existence :
    ∀ A B C : Point, ¬ Hilbert_neutral_basis.ColH A B C →
      ∃ p : Plane, IncidP A p ∧ IncidP B p ∧ IncidP C p
  one_point_on_plane :
    ∀ p : Plane, { A : Point // IncidP A p }
  plane_uniqueness :
    ∀ (A B C : Point) (p q : Plane),
      ¬ Hilbert_neutral_basis.ColH A B C →
      IncidP A p → IncidP B p → IncidP C p →
      IncidP A q → IncidP B q → IncidP C q →
      EqP p q
  line_on_plane :
    ∀ (A B : Point) (l : Line) (p : Plane),
      A ≠ B →
      IncidL A l → IncidL B l → IncidP A p → IncidP B p →
      @Hilbert_neutral_basis.IncidLP Point _ l p
  -- Group II Order
  between_diff : ∀ A B C : Point, BetH A B C → A ≠ C
  between_col : ∀ A B C : Point, BetH A B C → Hilbert_neutral_basis.ColH A B C
  between_comm : ∀ A B C : Point, BetH A B C → BetH C B A
  between_out : ∀ A B : Point, A ≠ B → ∃ C : Point, BetH A B C
  between_only_one : ∀ A B C : Point, BetH A B C → ¬ BetH B C A
  pasch :
    ∀ (A B C : Point) (l : Line) (p : Plane),
      ¬ Hilbert_neutral_basis.ColH A B C →
      IncidP A p → IncidP B p → IncidP C p →
      @Hilbert_neutral_basis.IncidLP Point _ l p →
      ¬ IncidL C l →
      @Hilbert_neutral_basis.cut Point _ l A B →
      @Hilbert_neutral_basis.cut Point _ l A C ∨
      @Hilbert_neutral_basis.cut Point _ l B C
  -- Group III Congruence
  cong_permr : ∀ A B C D : Point, CongH A B C D → CongH A B D C
  cong_existence :
    ∀ (A B A' P : Point) (l : Line),
      A ≠ B → A' ≠ P →
      IncidL A' l → IncidL P l →
      ∃ B' : Point, IncidL B' l ∧ Hilbert_neutral_basis.outH A' P B' ∧ CongH A' B' A B
  cong_pseudo_transitivity :
    ∀ A B C D E F : Point,
      CongH A B C D → CongH A B E F → CongH C D E F
  addition :
    ∀ A B C A' B' C' : Point,
      Hilbert_neutral_basis.ColH A B C → Hilbert_neutral_basis.ColH A' B' C' →
      Hilbert_neutral_basis.disjoint A B B C →
      Hilbert_neutral_basis.disjoint A' B' B' C' →
      CongH A B A' B' → CongH B C B' C' →
      CongH A C A' C'
  conga_refl :
    ∀ A B C : Point, ¬ Hilbert_neutral_basis.ColH A B C → CongaH A B C A B C
  conga_comm :
    ∀ A B C : Point, ¬ Hilbert_neutral_basis.ColH A B C → CongaH A B C C B A
  conga_permlr :
    ∀ A B C D E F : Point, CongaH A B C D E F → CongaH C B A F E D
  conga_out_conga :
    ∀ A B C D E F A' C' D' F' : Point,
      CongaH A B C D E F →
      Hilbert_neutral_basis.outH B A A' →
      Hilbert_neutral_basis.outH B C C' →
      Hilbert_neutral_basis.outH E D D' →
      Hilbert_neutral_basis.outH E F F' →
      CongaH A' B C' D' E F'
  cong_4_existence :
    ∀ A B C O X P : Point,
      ¬ Hilbert_neutral_basis.ColH P O X →
      ¬ Hilbert_neutral_basis.ColH A B C →
      ∃ Y : Point, CongaH A B C X O Y ∧ Hilbert_neutral_basis.same_side' P Y O X
  cong_4_uniqueness :
    ∀ A B C O P X Y Y' : Point,
      ¬ Hilbert_neutral_basis.ColH P O X →
      ¬ Hilbert_neutral_basis.ColH A B C →
      CongaH A B C X O Y → CongaH A B C X O Y' →
      Hilbert_neutral_basis.same_side' P Y O X →
      Hilbert_neutral_basis.same_side' P Y' O X →
      Hilbert_neutral_basis.outH O Y Y'
  cong_5 :
    ∀ A B C A' B' C' : Point,
      ¬ Hilbert_neutral_basis.ColH A B C → ¬ Hilbert_neutral_basis.ColH A' B' C' →
      CongH A B A' B' → CongH A C A' C' →
      CongaH B A C B' A' C' →
      CongaH A B C A' B' C'

/-! ## Hilbert neutral 2D -/

class Hilbert_neutral_2D (Point : Type)
    extends Hilbert_neutral_dimensionless Point where
  pasch_2D :
    ∀ (A B C : Point) (l : Line),
      ¬ Hilbert_neutral_basis.ColH A B C →
      ¬ IncidL C l →
      @Hilbert_neutral_basis.cut Point _ l A B →
      @Hilbert_neutral_basis.cut Point _ l A C ∨
      @Hilbert_neutral_basis.cut Point _ l B C

/-! ## Hilbert neutral 3D -/

class Hilbert_neutral_3D (Point : Type)
    extends Hilbert_neutral_dimensionless Point where
  plane_intersection :
    ∀ (A : Point) (p q : Plane),
      IncidP A p → IncidP A q →
      ∃ B : Point, IncidP B p ∧ IncidP B q ∧ A ≠ B
  HS1 : Point
  HS2 : Point
  HS3 : Point
  HS4 : Point
  lower_dim_3 :
    ¬ ∃ p : Plane, IncidP HS1 p ∧ IncidP HS2 p ∧ IncidP HS3 p ∧ IncidP HS4 p

/-! ## Hilbert euclidean -/

namespace Hilbert_euclidean

variable {Point : Type} [self : Hilbert_neutral_dimensionless Point]

def Para (l m : self.Line) : Prop :=
  (¬ ∃ X : Point, self.IncidL X l ∧ self.IncidL X m) ∧
  ∃ p : self.Plane,
    @Hilbert_neutral_basis.IncidLP Point _ l p ∧
    @Hilbert_neutral_basis.IncidLP Point _ m p

end Hilbert_euclidean

class Hilbert_euclidean (Point : Type)
    extends Hilbert_neutral_dimensionless Point where
  euclid_uniqueness :
    ∀ (l : Line) (P : Point) (m1 m2 : Line),
      ¬ IncidL P l →
      @Hilbert_euclidean.Para Point _ l m1 → IncidL P m1 →
      @Hilbert_euclidean.Para Point _ l m2 → IncidL P m2 →
      EqL m1 m2

/-! ## Hilbert euclidean with intersection-decidability -/

class Hilbert_euclidean_ID (Point : Type)
    extends Hilbert_euclidean Point where
  decidability_of_intersection :
    ∀ l m : Line,
      (∃ I : Point, IncidL I l ∧ IncidL I m) ∨
      ¬ (∃ I : Point, IncidL I l ∧ IncidL I m)
