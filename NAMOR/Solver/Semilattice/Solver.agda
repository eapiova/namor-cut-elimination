{-# OPTIONS --safe #-}

module NAMOR.Solver.Semilattice.Solver where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool using (Bool; true; false; _and_; if_then_else_)
open import Cubical.Data.Empty as ⊥ using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.FinData.Properties using (discreteFin)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (Unit*; tt*)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Relation.Nullary using (Discrete; yes; no)

open import Cubical.Algebra.Semilattice

open import NAMOR.Solver.Semilattice.Expression

private
  variable
    ℓ : Level

module SemilatticeSolve (L : Semilattice ℓ) where
  open Eval L public
  open SemilatticeStr (snd L) renaming (_·_ to _∨l_; ε to 0l)
  open JoinSemilattice L

  ≤-trans : {x y z : ⟨ L ⟩} → x ≤ y → y ≤ z → x ≤ z
  ≤-trans {x} {y} {z} x≤y y≤z =
    x ∨l z       ≡⟨ cong (x ∨l_) (sym y≤z) ⟩
    x ∨l (y ∨l z) ≡⟨ ·Assoc _ _ _ ⟩
    (x ∨l y) ∨l z ≡⟨ cong (_∨l z) x≤y ⟩
    y ∨l z        ≡⟨ y≤z ⟩
    z ∎

  ≤-antisym : {x y : ⟨ L ⟩} → x ≤ y → y ≤ x → x ≡ y
  ≤-antisym {x} {y} x≤y y≤x = sym y≤x ∙∙ ·Comm _ _ ∙∙ x≤y

  NormalForm : ℕ → Type
  NormalForm n = List (Fin n)

  evalNF : {n : ℕ} → NormalForm n → Env n → ⟨ L ⟩
  evalNF [] ρ = 0l
  evalNF (i ∷ is) ρ = lookup i ρ ∨l evalNF is ρ

  flatten : {n : ℕ} → Expr n → NormalForm n
  flatten (∣ i) = i ∷ []
  flatten ε∨ = []
  flatten (e₁ ∨ₑ e₂) = flatten e₁ ++ flatten e₂

  evalNF-++ : {n : ℕ} (xs ys : NormalForm n) (ρ : Env n)
            → evalNF (xs ++ ys) ρ ≡ evalNF xs ρ ∨l evalNF ys ρ
  evalNF-++ [] ys ρ = sym (·IdL _)
  evalNF-++ (i ∷ is) ys ρ =
    cong (lookup i ρ ∨l_) (evalNF-++ is ys ρ) ∙ ·Assoc _ _ _

  isCorrect : {n : ℕ} (e : Expr n) (ρ : Env n)
            → evalNF (flatten e) ρ ≡ ⟦ e ⟧ ρ
  isCorrect (∣ i) ρ = ·IdR _
  isCorrect ε∨ ρ = refl
  isCorrect (e₁ ∨ₑ e₂) ρ =
    evalNF-++ (flatten e₁) (flatten e₂) ρ
    ∙ cong₂ _∨l_ (isCorrect e₁ ρ) (isCorrect e₂ ρ)

  _∈?_ : {n : ℕ} → Fin n → NormalForm n → Bool
  i ∈? [] = false
  i ∈? (j ∷ js) with discreteFin i j
  ... | yes _ = true
  ... | no  _ = i ∈? js

  _⊆?_ : {n : ℕ} → NormalForm n → NormalForm n → Bool
  [] ⊆? rhs = true
  (i ∷ is) ⊆? rhs = (i ∈? rhs) and (is ⊆? rhs)

  true≢false : true ≡ false → ⊥
  true≢false p = subst (λ b → if b then Unit* else ⊥) p tt*

  false≢true : false ≡ true → ⊥
  false≢true p = subst (λ b → if b then ⊥ else Unit*) p tt*

  and-left : {a b : Bool} → a and b ≡ true → a ≡ true
  and-left {true} {true} _ = refl
  and-left {true} {false} p = ⊥-rec (false≢true p)
  and-left {false} p = ⊥-rec (false≢true p)

  and-right : {a b : Bool} → a and b ≡ true → b ≡ true
  and-right {true} {true} _ = refl
  and-right {true} {false} p = ⊥-rec (false≢true p)
  and-right {false} p = ⊥-rec (false≢true p)

  ∈?-sound : {n : ℕ} (i : Fin n) (nf : NormalForm n) (ρ : Env n)
           → i ∈? nf ≡ true
           → lookup i ρ ≤ evalNF nf ρ
  ∈?-sound i [] ρ p = ⊥-rec (false≢true p)
  ∈?-sound i (j ∷ js) ρ p with discreteFin i j
  ... | yes i≡j = subst (λ k → lookup k ρ ≤ lookup j ρ ∨l evalNF js ρ) (sym i≡j) (∨≤RCancel _ _)
  ... | no  _   = ≤-trans (∈?-sound i js ρ p) (∨≤LCancel _ _)

  ⊆?-sound : {n : ℕ} (lhs rhs : NormalForm n) (ρ : Env n)
           → lhs ⊆? rhs ≡ true
           → evalNF lhs ρ ≤ evalNF rhs ρ
  ⊆?-sound [] rhs ρ _ = ·IdL _
  ⊆?-sound (i ∷ is) rhs ρ p =
    let i-in   = and-left p
        is-sub = and-right p
    in ∨lIsMax _ _ _ (∈?-sound i rhs ρ i-in) (⊆?-sound is rhs ρ is-sub)

  solve≤ : {n : ℕ}
         → (e₁ e₂ : Expr n)
         → (ρ : Env n)
         → {pf : flatten e₁ ⊆? flatten e₂ ≡ true}
         → ⟦ e₁ ⟧ ρ ≤ ⟦ e₂ ⟧ ρ
  solve≤ e₁ e₂ ρ {pf} =
    let nf-order = ⊆?-sound (flatten e₁) (flatten e₂) ρ pf
    in subst2 _≤_ (isCorrect e₁ ρ) (isCorrect e₂ ρ) nf-order

  solveEq : {n : ℕ}
          → (e₁ e₂ : Expr n)
          → (ρ : Env n)
          → {pf₁ : flatten e₁ ⊆? flatten e₂ ≡ true}
          → {pf₂ : flatten e₂ ⊆? flatten e₁ ≡ true}
          → ⟦ e₁ ⟧ ρ ≡ ⟦ e₂ ⟧ ρ
  solveEq e₁ e₂ ρ {pf₁} {pf₂} =
    ≤-antisym (solve≤ e₁ e₂ ρ {pf₁}) (solve≤ e₂ e₁ ρ {pf₂})
