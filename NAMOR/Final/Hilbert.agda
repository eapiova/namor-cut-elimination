{-# OPTIONS --safe #-}

module NAMOR.Final.Hilbert where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit)

open import NAMOR.Final.Syntax

private variable
  M : Logic
  A B C : Formula

HasD : Logic → Type
HasD D  = Unit
HasD D4 = Unit
HasD _  = ⊥

HasT : Logic → Type
HasT T      = Unit
HasT S4     = Unit
HasT S4dot2 = Unit
HasT S5     = Unit
HasT _      = ⊥

Has4 : Logic → Type
Has4 K4     = Unit
Has4 D4     = Unit
Has4 S4     = Unit
Has4 S4dot2 = Unit
Has4 _      = ⊥

Has5 : Logic → Type
Has5 S5 = Unit
Has5 _  = ⊥

HasC : Logic → Type
HasC S4dot2 = Unit
HasC _      = ⊥

data Axiom (M : Logic) : Formula → Type where
  -- Propositional
  P1 : Axiom M (A ⇒ (B ⇒ A))
  P2 : Axiom M ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
  P3 : Axiom M (((Not B) ⇒ (Not A)) ⇒ (((Not B) ⇒ A) ⇒ B))

  -- Modal base
  AxK : Axiom M (□ (A ⇒ B) ⇒ (□ A ⇒ □ B))
  AxDual1 : Axiom M (♢ A ⇒ Not (□ (Not A)))
  AxDual2 : Axiom M (Not (□ (Not A)) ⇒ ♢ A)

  -- Logic-specific
  AxD : HasD M → Axiom M (□ A ⇒ ♢ A)
  AxT : HasT M → Axiom M (□ A ⇒ A)
  Ax4 : Has4 M → Axiom M (□ A ⇒ □ (□ A))
  Ax5 : Has5 M → Axiom M (♢ A ⇒ □ (♢ A))
  AxC : HasC M → Axiom M (♢ (□ A) ⇒ □ (♢ A))

infix 3 _⊢ₕ_

-- %<*hilbertJudgement>
data _⊢ₕ_ (M : Logic) : Formula → Type where
  ax  : Axiom M A → M ⊢ₕ A
  MP  : M ⊢ₕ A → M ⊢ₕ (A ⇒ B) → M ⊢ₕ B
  NEC : M ⊢ₕ A → M ⊢ₕ (□ A)
-- %</hilbertJudgement>
