{-# OPTIONS --safe #-}

module NAMOR.Final.Syntax where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List using (List; _∷_; []; _++_; [_]; map)
open import Cubical.Data.List.Properties
  using (++-assoc; discreteList)
open import NAMOR.List.Any
  using (Any; here; there; Any-map⁺)
open import NAMOR.List.RemoveAll
open import NAMOR.List.Membership
  using (_∈_; _∉_; _⊆_; ∈-here; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import NAMOR.List.Prefix
  using (Prefix; _⊑_; ⊑-refl; ⊑-trans; ⊑-++; ⊑-dec;
         suffix; suffix-correct)
  renaming ([] to ⊑[]; _∷_ to _⊑∷_)
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary

-- Tokens are natural numbers
Token : Type
Token = ℕ

-- Positions are sequences of tokens
Position : Type
Position = List Token

-- Propositional symbols (natural numbers, not strings)
Prop : Type
Prop = ℕ

-- Modal formulas
-- %<*formulaType>
data Formula : Type where
  atom : Prop → Formula
  bot  : Formula
  _⇒_  : Formula → Formula → Formula
  And  : Formula → Formula → Formula
  Or   : Formula → Formula → Formula
  Not  : Formula → Formula
  □_   : Formula → Formula
  ♢_   : Formula → Formula

infixr 5 _⇒_
infixl 6 And Or
infix 7 Not □_ ♢_

syntax And A B = A ∧ B
syntax Or A B = A ∨ B
syntax Not A = ¬ A
-- %</formulaType>

-- Position-formula: a formula labelled with a position
-- %<*pformulaType>
record PFormula : Type where
  constructor _^_
  field
    form : Formula
    pos  : Position

infix 4 _^_

-- Context = list of position-formulas
Ctx : Type
Ctx = List PFormula
-- %</pformulaType>

-- Position concatenation
_∘_ : Position → Position → Position
α ∘ β = α ++ β

infixr 5 _∘_

------------------------------------------------------------------------
-- Position relations

-- %<*positionRelations>
-- Strict prefix (α ⊏ β): α is a proper prefix of β
_⊏_ : Position → Position → Type
α ⊏ β = (α ⊑ β) × (α ≡ β → ⊥)

infix 4 _⊏_

-- Successor (α ◃ β): β = α ++ [z] for some token z
_◃_ : Position → Position → Type
α ◃ β = Σ Token λ z → β ≡ α ++ [ z ]

-- Reflexive successor
_◃⁰_ : Position → Position → Type
α ◃⁰ β = (α ≡ β) ⊎ (α ◃ β)

-- Set-subset on positions (for S4.2)
_⊆ₛ_ : Position → Position → Type
α ⊆ₛ β = α ⊆ β

-- Sentinel: β appears embedded in some position in Γ
_has_ : Ctx → Position → Type
Γ has β = Any (λ φ → Σ Position λ γ →
  Σ Position λ η → PFormula.pos φ ≡ γ ++ β ++ η) Γ

infix 4 _◃_ _◃⁰_ _⊆ₛ_
-- %</positionRelations>

------------------------------------------------------------------------
-- Logic and constraint functions

-- %<*logicType>
data Logic : Type where
  K D T K4 D4 S4 S4dot2 S5 : Logic
-- %</logicType>

-- Modal constraint (Table 1 of OVERLAY25 paper)
-- %<*modalConstraint>
modalConstraint : Logic → Position → Position
               → Ctx → Ctx → Type
modalConstraint S5     α β Γ Δ = Unit
modalConstraint S4dot2 α β Γ Δ = α ⊆ₛ β
modalConstraint S4     α β Γ Δ = α ⊑ β
modalConstraint T      α β Γ Δ = α ◃⁰ β
modalConstraint D      α β Γ Δ = α ◃ β
modalConstraint D4     α β Γ Δ = α ⊏ β
modalConstraint K4     α β Γ Δ = (α ⊏ β) × ((Γ ++ Δ) has β)
modalConstraint K      α β Γ Δ = (α ◃ β) × ((Γ ++ Δ) has β)
-- %</modalConstraint>

------------------------------------------------------------------------
-- Init membership (relational, S4dot2 style)

_∈Init_ : Position → Ctx → Type
t ∈Init Γ = Σ PFormula λ pf →
  (pf ∈ Γ) × (t ⊑ PFormula.pos pf)

_∉Init_ : Position → Ctx → Type
t ∉Init Γ = t ∈Init Γ → ⊥

------------------------------------------------------------------------
-- Decidable equality

-- Formula equality
discreteFormula : Discrete Formula
discreteFormula (atom p) (atom q) with discreteℕ p q
... | yes e = yes (cong atom e)
... | no ¬e = no λ e → ¬e (atomInj e)
  where
  atomInj : atom p ≡ atom q → p ≡ q
  atomInj e = cong (λ where (atom x) → x; _ → 0) e
discreteFormula bot bot = yes refl
discreteFormula (A ⇒ B) (C ⇒ E) with discreteFormula A C
... | no ¬e = no λ e → ¬e (cong (λ where (x ⇒ _) → x; _ → bot) e)
... | yes eA with discreteFormula B E
... | yes eB = yes (cong₂ _⇒_ eA eB)
... | no ¬e = no λ e → ¬e (cong (λ where (_ ⇒ x) → x; _ → bot) e)
discreteFormula (And A B) (And C E) with discreteFormula A C
... | no ¬e = no λ e → ¬e (cong (λ where (And x _) → x; _ → bot) e)
... | yes eA with discreteFormula B E
... | yes eB = yes (cong₂ And eA eB)
... | no ¬e = no λ e → ¬e (cong (λ where (And _ x) → x; _ → bot) e)
discreteFormula (Or A B) (Or C E) with discreteFormula A C
... | no ¬e = no λ e → ¬e (cong (λ where (Or x _) → x; _ → bot) e)
... | yes eA with discreteFormula B E
... | yes eB = yes (cong₂ Or eA eB)
... | no ¬e = no λ e → ¬e (cong (λ where (Or _ x) → x; _ → bot) e)
discreteFormula (Not A) (Not B) with discreteFormula A B
... | yes e = yes (cong Not e)
... | no ¬e = no λ e → ¬e (cong (λ where (Not x) → x; _ → bot) e)
discreteFormula (□ A) (□ B) with discreteFormula A B
... | yes e = yes (cong □_ e)
... | no ¬e = no λ e → ¬e (cong (λ where (□ x) → x; _ → bot) e)
discreteFormula (♢ A) (♢ B) with discreteFormula A B
... | yes e = yes (cong ♢_ e)
... | no ¬e = no λ e → ¬e (cong (λ where (♢ x) → x; _ → bot) e)
-- Cross-constructor cases (all no)
discreteFormula (atom _) bot = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (atom _) = Unit; F _ = ⊥
discreteFormula (atom _) (_ ⇒ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (atom _) = Unit; F _ = ⊥
discreteFormula (atom _) (And _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (atom _) = Unit; F _ = ⊥
discreteFormula (atom _) (Or _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (atom _) = Unit; F _ = ⊥
discreteFormula (atom _) (Not _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (atom _) = Unit; F _ = ⊥
discreteFormula (atom _) (□ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (atom _) = Unit; F _ = ⊥
discreteFormula (atom _) (♢ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (atom _) = Unit; F _ = ⊥
discreteFormula bot (atom _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F bot = Unit; F _ = ⊥
discreteFormula bot (_ ⇒ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F bot = Unit; F _ = ⊥
discreteFormula bot (And _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F bot = Unit; F _ = ⊥
discreteFormula bot (Or _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F bot = Unit; F _ = ⊥
discreteFormula bot (Not _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F bot = Unit; F _ = ⊥
discreteFormula bot (□ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F bot = Unit; F _ = ⊥
discreteFormula bot (♢ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F bot = Unit; F _ = ⊥
discreteFormula (_ ⇒ _) (atom _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (_ ⇒ _) = Unit; F _ = ⊥
discreteFormula (_ ⇒ _) bot = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (_ ⇒ _) = Unit; F _ = ⊥
discreteFormula (_ ⇒ _) (And _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (_ ⇒ _) = Unit; F _ = ⊥
discreteFormula (_ ⇒ _) (Or _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (_ ⇒ _) = Unit; F _ = ⊥
discreteFormula (_ ⇒ _) (Not _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (_ ⇒ _) = Unit; F _ = ⊥
discreteFormula (_ ⇒ _) (□ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (_ ⇒ _) = Unit; F _ = ⊥
discreteFormula (_ ⇒ _) (♢ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (_ ⇒ _) = Unit; F _ = ⊥
discreteFormula (And _ _) (atom _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (And _ _) = Unit; F _ = ⊥
discreteFormula (And _ _) bot = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (And _ _) = Unit; F _ = ⊥
discreteFormula (And _ _) (_ ⇒ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (And _ _) = Unit; F _ = ⊥
discreteFormula (And _ _) (Or _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (And _ _) = Unit; F _ = ⊥
discreteFormula (And _ _) (Not _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (And _ _) = Unit; F _ = ⊥
discreteFormula (And _ _) (□ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (And _ _) = Unit; F _ = ⊥
discreteFormula (And _ _) (♢ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (And _ _) = Unit; F _ = ⊥
discreteFormula (Or _ _) (atom _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Or _ _) = Unit; F _ = ⊥
discreteFormula (Or _ _) bot = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Or _ _) = Unit; F _ = ⊥
discreteFormula (Or _ _) (_ ⇒ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Or _ _) = Unit; F _ = ⊥
discreteFormula (Or _ _) (And _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Or _ _) = Unit; F _ = ⊥
discreteFormula (Or _ _) (Not _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Or _ _) = Unit; F _ = ⊥
discreteFormula (Or _ _) (□ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Or _ _) = Unit; F _ = ⊥
discreteFormula (Or _ _) (♢ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Or _ _) = Unit; F _ = ⊥
discreteFormula (Not _) (atom _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Not _) = Unit; F _ = ⊥
discreteFormula (Not _) bot = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Not _) = Unit; F _ = ⊥
discreteFormula (Not _) (_ ⇒ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Not _) = Unit; F _ = ⊥
discreteFormula (Not _) (And _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Not _) = Unit; F _ = ⊥
discreteFormula (Not _) (Or _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Not _) = Unit; F _ = ⊥
discreteFormula (Not _) (□ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Not _) = Unit; F _ = ⊥
discreteFormula (Not _) (♢ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (Not _) = Unit; F _ = ⊥
discreteFormula (□ _) (atom _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (□ _) = Unit; F _ = ⊥
discreteFormula (□ _) bot = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (□ _) = Unit; F _ = ⊥
discreteFormula (□ _) (_ ⇒ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (□ _) = Unit; F _ = ⊥
discreteFormula (□ _) (And _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (□ _) = Unit; F _ = ⊥
discreteFormula (□ _) (Or _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (□ _) = Unit; F _ = ⊥
discreteFormula (□ _) (Not _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (□ _) = Unit; F _ = ⊥
discreteFormula (□ _) (♢ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (□ _) = Unit; F _ = ⊥
discreteFormula (♢ _) (atom _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (♢ _) = Unit; F _ = ⊥
discreteFormula (♢ _) bot = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (♢ _) = Unit; F _ = ⊥
discreteFormula (♢ _) (_ ⇒ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (♢ _) = Unit; F _ = ⊥
discreteFormula (♢ _) (And _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (♢ _) = Unit; F _ = ⊥
discreteFormula (♢ _) (Or _ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (♢ _) = Unit; F _ = ⊥
discreteFormula (♢ _) (Not _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (♢ _) = Unit; F _ = ⊥
discreteFormula (♢ _) (□ _) = no λ e → ⊥.rec (subst F e tt) where F : Formula → Type; F (♢ _) = Unit; F _ = ⊥

_≟F_ : (A B : Formula) → Dec (A ≡ B)
_≟F_ = discreteFormula

_≟P_ : (α β : Position) → Dec (α ≡ β)
_≟P_ = discreteList discreteℕ

-- PFormula decidable equality
_≟pf_ : (φ ψ : PFormula) → Dec (φ ≡ ψ)
(A ^ α) ≟pf (B ^ β) with A ≟F B | α ≟P β
... | yes eA | yes eα = yes (λ i → eA i ^ eα i)
... | yes _  | no ¬eα = no λ e → ¬eα (cong PFormula.pos e)
... | no ¬eA | _      = no λ e → ¬eA (cong PFormula.form e)

-- PFormula removal from context (canonical removeAll)

_≟pfʳ_ : Discrete PFormula
_≟pfʳ_ φ ψ with ψ ≟pf φ
... | yes eq = yes (sym eq)
... | no neq = no (λ p → neq (sym p))

private
  module PFRemoveAll = RemoveAll _≟pfʳ_

_-pf_ : Ctx → PFormula → Ctx
Γ -pf φ = PFRemoveAll.removeAll φ Γ

------------------------------------------------------------------------
-- Cut constraint (Table 2 of OVERLAY25 paper)

-- %<*cutConstraint>
cutConstraint : Logic → Formula → Position
             → Ctx → Ctx → Ctx → Ctx → Type
cutConstraint K  A α Γ₁ Γ₂ Δ₁ Δ₂ =
  (α ∈Init (Γ₁ ++ (Δ₁ -pf (A ^ α))))
  ⊎ (α ∈Init ((Γ₂ -pf (A ^ α)) ++ Δ₂))
cutConstraint K4 A α Γ₁ Γ₂ Δ₁ Δ₂ =
  (α ∈Init (Γ₁ ++ (Δ₁ -pf (A ^ α))))
  ⊎ (α ∈Init ((Γ₂ -pf (A ^ α)) ++ Δ₂))
cutConstraint _  _ _ _  _  _  _  = Unit
-- %</cutConstraint>

------------------------------------------------------------------------
-- Prefix substitution

-- Decidable prefix using Prefix data type
isPrefix : (α γ : Position) → Dec (α ⊑ γ)
isPrefix = ⊑-dec discreteℕ

-- Substitution: replace prefix α with β in γ
substPos : (α β γ : Position) → Position
substPos α β γ with isPrefix α γ
... | yes p = β ∘ suffix p
... | no _  = γ

substPFormula : (α β : Position) → PFormula → PFormula
substPFormula α β (A ^ γ) = A ^ substPos α β γ

substContext : (α β : Position) → Ctx → Ctx
substContext α β Γ = map (substPFormula α β) Γ

-- substContext distributes over ++
substContext-++ : (α β : Position) (Γ Δ : Ctx)
  → substContext α β (Γ ++ Δ)
  ≡ substContext α β Γ ++ substContext α β Δ
substContext-++ α β [] Δ = refl
substContext-++ α β (x ∷ Γ) Δ =
  cong (substPFormula α β x ∷_) (substContext-++ α β Γ Δ)
