/-
Translated from theories/Axioms/tarski_axioms.v.

Axioms of Tarski as given in
  Wolfram Schwabhäuser, Wanda Szmielew and Alfred Tarski,
  Metamathematische Methoden in der Geometrie, Springer-Verlag, Berlin, 1983.
-/

class Tarski_neutral_dimensionless (Tpoint : Type) where
  Bet : Tpoint → Tpoint → Tpoint → Prop
  Cong : Tpoint → Tpoint → Tpoint → Tpoint → Prop
  cong_pseudo_reflexivity : ∀ A B : Tpoint, Cong A B B A
  cong_inner_transitivity : ∀ A B C D E F : Tpoint,
    Cong A B C D → Cong A B E F → Cong C D E F
  cong_identity : ∀ A B C : Tpoint, Cong A B C C → A = B
  segment_construction : ∀ A B C D : Tpoint,
    ∃ E, Bet A B E ∧ Cong B E C D
  five_segment : ∀ A A' B B' C C' D D' : Tpoint,
    Cong A B A' B' →
    Cong B C B' C' →
    Cong A D A' D' →
    Cong B D B' D' →
    Bet A B C → Bet A' B' C' → A ≠ B → Cong C D C' D'
  between_identity : ∀ A B : Tpoint, Bet A B A → A = B
  inner_pasch : ∀ A B C P Q : Tpoint,
    Bet A P C → Bet B Q C →
    ∃ X, Bet P X B ∧ Bet Q X A
  PA : Tpoint
  PB : Tpoint
  PC : Tpoint
  lower_dim : ¬ (Bet PA PB PC ∨ Bet PB PC PA ∨ Bet PC PA PB)

class Tarski_neutral_dimensionless_with_decidable_point_equality (Tpoint : Type)
    extends Tarski_neutral_dimensionless Tpoint where
  point_equality_decidability : ∀ A B : Tpoint, A = B ∨ A ≠ B

class Tarski_2D (Tpoint : Type)
    extends Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint where
  upper_dim : ∀ A B C P Q : Tpoint,
    P ≠ Q → Cong A P A Q → Cong B P B Q → Cong C P C Q →
    (Bet A B C ∨ Bet B C A ∨ Bet C A B)

class Tarski_3D (Tpoint : Type)
    extends Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint where
  S1 : Tpoint
  S2 : Tpoint
  S3 : Tpoint
  S4 : Tpoint
  lower_dim_3 : ¬ ∃ X,
    (Bet S1 S2 X ∨ Bet S2 X S1 ∨ Bet X S1 S2) ∧ (Bet S3 S4 X ∨ Bet S4 X S3 ∨ Bet X S3 S4) ∨
    (Bet S1 S3 X ∨ Bet S3 X S1 ∨ Bet X S1 S3) ∧ (Bet S2 S4 X ∨ Bet S4 X S2 ∨ Bet X S2 S4) ∨
    (Bet S1 S4 X ∨ Bet S4 X S1 ∨ Bet X S1 S4) ∧ (Bet S2 S3 X ∨ Bet S3 X S2 ∨ Bet X S2 S3)
  upper_dim_3 : ∀ A B C P Q R : Tpoint,
    P ≠ Q → Q ≠ R → P ≠ R →
    Cong A P A Q → Cong B P B Q → Cong C P C Q →
    Cong A P A R → Cong B P B R → Cong C P C R →
    (Bet A B C ∨ Bet B C A ∨ Bet C A B)

class Tarski_euclidean (Tpoint : Type)
    extends Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint where
  euclid : ∀ A B C D T : Tpoint,
    Bet A D T → Bet B D C → A ≠ D →
    ∃ X Y, Bet A B X ∧ Bet A C Y ∧ Bet X T Y

class Tarski_ruler_and_compass (Tpoint : Type)
    extends Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint where
  circle_circle_continuity : ∀ A B C D B' D' : Tpoint,
    Cong A B' A B → Cong C D' C D →
    Bet A D' B → Bet C B' D →
    ∃ Z, Cong A Z A B ∧ Cong C Z C D

class Tarski_continuous (Tpoint : Type)
    extends Tarski_neutral_dimensionless_with_decidable_point_equality Tpoint where
  continuity : ∀ (Alpha Beta : Tpoint → Prop),
    (∃ A, ∀ X Y, Alpha X → Beta Y → Bet A X Y) →
    (∃ B, ∀ X Y, Alpha X → Beta Y → Bet X B Y)
