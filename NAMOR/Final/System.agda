{-# OPTIONS --safe #-}

-- Unified proof system for modal logics K through S5.
-- OVERLAY25 paper, Section 4.
-- Module parameterized by Logic to select modal constraints.

open import NAMOR.Final.Syntax using (Logic)

module NAMOR.Final.System (M : Logic) where

open import NAMOR.Final.Syntax
  hiding (Logic; K; D; T; K4; D4; S4; S4dot2; S5)

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List using (List; []; _∷_; _++_; [_])
open import Cubical.Data.Nat using (ℕ)

private variable
  Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : Ctx
  A B : Formula
  α β : Position
  x : Token

data _⊢_ : Ctx → Ctx → Type where

  -- %<*identityCut>
  -- Identity
  Ax : [ (A ^ α) ] ⊢ [ (A ^ α) ]

  -- Cut
  Cut : cutConstraint M A α Γ₁ Γ₂ Δ₁ Δ₂
    → Γ₁ ⊢ ([ (A ^ α) ] ++ Δ₁)
    → (Γ₂ ++ [ (A ^ α) ]) ⊢ Δ₂
    → (Γ₁ ++ Γ₂) ⊢ (Δ₁ ++ Δ₂)
  -- %</identityCut>

  -- %<*structuralRules>
  -- Structural: Weakening
  WeakenL : Γ ⊢ Δ → ((A ^ α) ∷ Γ) ⊢ Δ
  WeakenR : Γ ⊢ Δ → Γ ⊢ ((A ^ α) ∷ Δ)

  -- Structural: Contraction
  ContractL
    : ((A ^ α) ∷ (A ^ α) ∷ Γ) ⊢ Δ
    → ((A ^ α) ∷ Γ) ⊢ Δ
  ContractR
    : Γ ⊢ ((A ^ α) ∷ (A ^ α) ∷ Δ)
    → Γ ⊢ ((A ^ α) ∷ Δ)

  -- Structural: Exchange
  ExchangeL
    : ∀ {C D : PFormula}
    → (Γ₁ ++ [ C ] ++ [ D ] ++ Γ₂) ⊢ Δ
    → (Γ₁ ++ [ D ] ++ [ C ] ++ Γ₂) ⊢ Δ
  ExchangeR
    : ∀ {C D : PFormula}
    → Γ ⊢ (Δ₁ ++ [ C ] ++ [ D ] ++ Δ₂)
    → Γ ⊢ (Δ₁ ++ [ D ] ++ [ C ] ++ Δ₂)
  -- %</structuralRules>

  -- %<*propositionalRules>
  -- Propositional: Negation
  NotL : Γ ⊢ ((A ^ α) ∷ Δ)
    → ((Not A ^ α) ∷ Γ) ⊢ Δ
  NotR : ((A ^ α) ∷ Γ) ⊢ Δ
    → Γ ⊢ ((Not A ^ α) ∷ Δ)

  -- Propositional: Conjunction
  AndL1 : ((A ^ α) ∷ Γ) ⊢ Δ
    → ((And A B ^ α) ∷ Γ) ⊢ Δ
  AndL2 : ((B ^ α) ∷ Γ) ⊢ Δ
    → ((And A B ^ α) ∷ Γ) ⊢ Δ
  AndR : Γ₁ ⊢ ((A ^ α) ∷ Δ₁)
    → Γ₂ ⊢ ((B ^ α) ∷ Δ₂)
    → (Γ₁ ++ Γ₂) ⊢ ((And A B ^ α) ∷ Δ₁ ++ Δ₂)

  -- Propositional: Disjunction
  OrL : ((A ^ α) ∷ Γ₁) ⊢ Δ₁
    → ((B ^ α) ∷ Γ₂) ⊢ Δ₂
    → ((Or A B ^ α) ∷ Γ₁ ++ Γ₂) ⊢ (Δ₁ ++ Δ₂)
  OrR1 : Γ ⊢ ((A ^ α) ∷ Δ)
    → Γ ⊢ ((Or A B ^ α) ∷ Δ)
  OrR2 : Γ ⊢ ((B ^ α) ∷ Δ)
    → Γ ⊢ ((Or A B ^ α) ∷ Δ)

  -- Propositional: Implication
  ImpL : Γ₁ ⊢ ((A ^ α) ∷ Δ₁)
    → ((B ^ α) ∷ Γ₂) ⊢ Δ₂
    → (((A ⇒ B) ^ α) ∷ Γ₁ ++ Γ₂) ⊢ (Δ₁ ++ Δ₂)
  ImpR : ((A ^ α) ∷ Γ) ⊢ ((B ^ α) ∷ Δ)
    → Γ ⊢ (((A ⇒ B) ^ α) ∷ Δ)
  -- %</propositionalRules>

  -- %<*modalRules>
  -- Modal: □ Left
  BoxL : ∀ {Γ Δ A α β}
    → modalConstraint M α β Γ Δ
    → (Γ ++ [ (A ^ β) ]) ⊢ Δ
    → (Γ ++ [ (□ A ^ α) ]) ⊢ Δ

  -- Modal: □ Right (eigentoken condition)
  BoxR : ∀ {Γ Δ A α x}
    → (α ∘ [ x ]) ∉Init (Γ ++ Δ)
    → Γ ⊢ ([ (A ^ (α ∘ [ x ])) ] ++ Δ)
    → Γ ⊢ ([ (□ A ^ α) ] ++ Δ)

  -- Modal: ♢ Left (eigentoken condition)
  DiaL : ∀ {Γ Δ A α x}
    → (α ∘ [ x ]) ∉Init (Γ ++ Δ)
    → (Γ ++ [ (A ^ (α ∘ [ x ])) ]) ⊢ Δ
    → (Γ ++ [ (♢ A ^ α) ]) ⊢ Δ

  -- Modal: ♢ Right
  DiaR : ∀ {Γ Δ A α β}
    → modalConstraint M α β Γ Δ
    → Γ ⊢ ([ (A ^ β) ] ++ Δ)
    → Γ ⊢ ([ (♢ A ^ α) ] ++ Δ)
  -- %</modalRules>

infix 3 _⊢_
