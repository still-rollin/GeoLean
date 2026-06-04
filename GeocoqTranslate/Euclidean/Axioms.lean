/-
Translated from theories/Axioms/euclidean_axioms.v.

Two-class split: structural primitives in `euclidean_neutral_basis`,
derived predicates as plain `def`s in the surrounding namespace, axioms
in `euclidean_neutral` extending the basis. This mirrors Coq's
`Definition` semantics — the derived predicates are fixed (cannot be
overridden by an instance) and transparent (can be unfolded in
downstream proofs).

The alternative considered (in-class default-valued fields) was
rejected because (a) Lean allows instances to override defaults,
breaking the cross-system equivalence theorems (Tarski ≡ Euclid ≡
Hilbert) which rely on canonical definitions, and (b) default-valued
fields are opaque from outside the class, so values like `InCirc B J`
cannot be constructed with the anonymous constructor.

Axiom systems used to formalize Euclid's Elements:
  1. euclidean_neutral_basis / euclidean_neutral  -- neutral geometry
  2. euclidean_neutral_ruler_compass              -- line/circle continuity
  3. euclidean_euclidean                          -- Euclid's 5th postulate
  4. area                                         -- equality of areas
-/

/-! ## Neutral geometry: structural basis -/

/-- Structural primitives of neutral euclidean geometry: carrier types
and the three primitive predicates. Split out so derived predicates
(`nCol`, `Col`, `OnCirc`, …) can be defined in the surrounding namespace
before the axiom class references them. -/
class euclidean_neutral_basis (Point : Type) where
  Circle : Type
  Cong : Point → Point → Point → Point → Prop
  BetS : Point → Point → Point → Prop
  CI : Circle → Point → Point → Point → Prop
  PA : Point
  PB : Point
  PC : Point

namespace euclidean_neutral_basis

variable {Point : Type} [self : euclidean_neutral_basis Point]

def nCol (A B C : Point) : Prop :=
  A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
  ¬ self.BetS A B C ∧ ¬ self.BetS A C B ∧ ¬ self.BetS B A C

def Col (A B C : Point) : Prop :=
  A = B ∨ A = C ∨ B = C ∨
  self.BetS B A C ∨ self.BetS A B C ∨ self.BetS A C B

def Cong_3 (A B C a b c : Point) : Prop :=
  self.Cong A B a b ∧ self.Cong B C b c ∧ self.Cong A C a c

def TS (P A B Q : Point) : Prop :=
  ∃ X, self.BetS P X Q ∧ Col A B X ∧ nCol A B P

def Triangle (A B C : Point) : Prop := nCol A B C

def OnCirc (B : Point) (J : self.Circle) : Prop :=
  ∃ X Y U : Point, self.CI J U X Y ∧ self.Cong U B X Y

def InCirc (P : Point) (J : self.Circle) : Prop :=
  ∃ X Y U V W : Point, self.CI J U V W ∧
    (P = U ∨ (self.BetS U Y X ∧ self.Cong U X V W ∧ self.Cong U P U Y))

def OutCirc (P : Point) (J : self.Circle) : Prop :=
  ∃ X U V W : Point, self.CI J U V W ∧ self.BetS U X P ∧ self.Cong U X V W

end euclidean_neutral_basis

/-! ## Neutral geometry: axioms -/

class euclidean_neutral (Point : Type) extends euclidean_neutral_basis Point where
  cn_congruencetransitive :
    ∀ B C D E P Q : Point, Cong P Q B C → Cong P Q D E → Cong B C D E
  cn_congruencereflexive :
    ∀ A B : Point, Cong A B A B
  cn_equalityreverse :
    ∀ A B : Point, Cong A B B A
  cn_sumofparts :
    ∀ A B C a b c : Point,
      Cong A B a b → Cong B C b c → BetS A B C → BetS a b c → Cong A C a c
  cn_stability :
    ∀ A B : Point, ¬ A ≠ B → A = B
  axiom_circle_center_radius :
    ∀ (A B C : Point) (J : Circle) (P : Point),
      CI J A B C → euclidean_neutral_basis.OnCirc P J → Cong A P B C
  axiom_lower_dim : euclidean_neutral_basis.nCol PA PB PC
  axiom_betweennessidentity :
    ∀ A B : Point, ¬ BetS A B A
  axiom_betweennesssymmetry :
    ∀ A B C : Point, BetS A B C → BetS C B A
  axiom_innertransitivity :
    ∀ A B C D : Point,
      BetS A B D → BetS B C D → BetS A B C
  axiom_connectivity :
    ∀ A B C D : Point,
      BetS A B D → BetS A C D → ¬ BetS A B C → ¬ BetS A C B →
      B = C
  axiom_nocollapse :
    ∀ A B C D : Point, A ≠ B → Cong A B C D → C ≠ D
  axiom_5_line :
    ∀ A B C D a b c d : Point,
      Cong B C b c → Cong A D a d → Cong B D b d →
      BetS A B C → BetS a b c → Cong A B a b →
      Cong D C d c
  postulate_Pasch_inner :
    ∀ A B C P Q : Point,
      BetS A P C → BetS B Q C → euclidean_neutral_basis.nCol A C B →
      ∃ X, BetS A X Q ∧ BetS B X P
  postulate_Pasch_outer :
    ∀ A B C P Q : Point,
      BetS A P C → BetS B C Q → euclidean_neutral_basis.nCol B Q A →
      ∃ X, BetS A X Q ∧ BetS B P X
  postulate_Euclid2 :
    ∀ A B : Point, A ≠ B → ∃ X, BetS A B X
  postulate_Euclid3 :
    ∀ A B : Point, A ≠ B → ∃ X : Circle, CI X A A B

/-! ## Ruler-and-compass continuity -/

class euclidean_neutral_ruler_compass (Point : Type)
    extends euclidean_neutral Point where
  postulate_line_circle :
    ∀ (A B C : Point) (K : Circle) (P Q : Point),
      CI K C P Q → @euclidean_neutral_basis.InCirc Point _ B K → A ≠ B →
      ∃ X Y, euclidean_neutral_basis.Col A B X ∧ BetS A B Y ∧
        @euclidean_neutral_basis.OnCirc Point _ X K ∧
        @euclidean_neutral_basis.OnCirc Point _ Y K ∧
        BetS X B Y
  postulate_circle_circle :
    ∀ (C D F G : Point) (J K : Circle) (P Q R S : Point),
      CI J C R S → @euclidean_neutral_basis.InCirc Point _ P J →
      @euclidean_neutral_basis.OutCirc Point _ Q J → CI K D F G →
      @euclidean_neutral_basis.OnCirc Point _ P K →
      @euclidean_neutral_basis.OnCirc Point _ Q K →
      ∃ X, @euclidean_neutral_basis.OnCirc Point _ X J ∧
        @euclidean_neutral_basis.OnCirc Point _ X K

/-! ## Euclid's fifth postulate -/

class euclidean_euclidean (Point : Type)
    extends euclidean_neutral_ruler_compass Point where
  postulate_Euclid5 :
    ∀ a p q r s t : Point,
      BetS r t s → BetS p t q → BetS r a q →
      Cong p t q t → Cong t r t s → euclidean_neutral_basis.nCol p q s →
      ∃ X, BetS p a X ∧ BetS s q X

/-! ## Equality of areas -/

class area (Point : Type) extends euclidean_euclidean Point where
  EF : Point → Point → Point → Point → Point → Point → Point → Point → Prop
  ET : Point → Point → Point → Point → Point → Point → Prop
  axiom_congruentequal :
    ∀ A B C a b c : Point,
      euclidean_neutral_basis.Cong_3 A B C a b c → ET A B C a b c
  axiom_ETpermutation :
    ∀ A B C a b c : Point,
      ET A B C a b c →
      ET A B C b c a ∧
      ET A B C a c b ∧
      ET A B C b a c ∧
      ET A B C c b a ∧
      ET A B C c a b
  axiom_ETsymmetric :
    ∀ A B C a b c : Point, ET A B C a b c → ET a b c A B C
  axiom_EFpermutation :
    ∀ A B C D a b c d : Point,
      EF A B C D a b c d →
        EF A B C D b c d a ∧
        EF A B C D d c b a ∧
        EF A B C D c d a b ∧
        EF A B C D b a d c ∧
        EF A B C D d a b c ∧
        EF A B C D c b a d ∧
        EF A B C D a d c b
  axiom_halvesofequals :
    ∀ A B C D a b c d : Point,
      ET A B C B C D →
      euclidean_neutral_basis.TS A B C D → ET a b c b c d →
      euclidean_neutral_basis.TS a b c d → EF A B D C a b d c → ET A B C a b c
  axiom_EFsymmetric :
    ∀ A B C D a b c d : Point,
      EF A B C D a b c d → EF a b c d A B C D
  axiom_EFtransitive :
    ∀ A B C D P Q R S a b c d : Point,
      EF A B C D a b c d → EF a b c d P Q R S →
      EF A B C D P Q R S
  axiom_ETtransitive :
    ∀ A B C P Q R a b c : Point,
      ET A B C a b c → ET a b c P Q R → ET A B C P Q R
  axiom_cutoff1 :
    ∀ A B C D E a b c d e : Point,
      BetS A B C → BetS a b c → BetS E D C → BetS e d c →
      ET B C D b c d → ET A C E a c e →
      EF A B D E a b d e
  axiom_cutoff2 :
    ∀ A B C D E a b c d e : Point,
      BetS B C D → BetS b c d → ET C D E c d e → EF A B D E a b d e →
      EF A B C E a b c e
  axiom_paste1 :
    ∀ A B C D E a b c d e : Point,
      BetS A B C → BetS a b c → BetS E D C → BetS e d c →
      ET B C D b c d → EF A B D E a b d e →
      ET A C E a c e
  axiom_deZolt1 :
    ∀ B C D E : Point, BetS B E D → ¬ ET D B C E B C
  axiom_deZolt2 :
    ∀ A B C E F : Point,
      euclidean_neutral_basis.Triangle A B C → BetS B E A → BetS B F C →
      ¬ ET A B C E B F
  axiom_paste2 :
    ∀ A B C D E M a b c d e m : Point,
      BetS B C D → BetS b c d → ET C D E c d e →
      EF A B C E a b c e →
      BetS A M D → BetS B M E →
      BetS a m d → BetS b m e →
      EF A B D E a b d e
  axiom_paste3 :
    ∀ A B C D M a b c d m : Point,
      ET A B C a b c → ET A B D a b d →
      BetS C M D →
      (BetS A M B ∨ A = M ∨ M = B) →
      BetS c m d →
      (BetS a m b ∨ a = m ∨ m = b) →
      EF A C B D a c b d
  axiom_paste4 :
    ∀ A B C D F G H J K L M P e m : Point,
      EF A B m D F K H G → EF D B e C G H M L →
      BetS A P C → BetS B P D → BetS K H M → BetS F G L →
      BetS B m D → BetS B e C → BetS F J M → BetS K J L →
      EF A B C D F K M L
