{-# OPTIONS --safe #-}

module NAMOR.Solver.Subset where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Relation.Nullary using (Discrete; yes; no)
open import Cubical.Data.Bool using (true)

open import Cubical.Data.List using (List; _∷_; []; _++_)
open import Cubical.Data.Maybe using (just; nothing)

open import NAMOR.List.Any renaming (here to hereA; there to thereA)
open import NAMOR.List.Membership as Mem
  using (_∈_; ∈-++⁺ˡ; ∈-++⁺ʳ)
  renaming (_⊆_ to _⊆ᵢ_)

private
  variable
    ℓ : Level

-- Re-export all solver modules
open import NAMOR.Solver.Subset.Core public
open import NAMOR.Solver.Subset.Normal public
open import NAMOR.Solver.Subset.Routing public

-- Solver interface parameterized by type with decidable equality
module Solver {A : Type ℓ} (_≟_ : Discrete A) where

  open Routing _≟_ public

  -- Main solver: given two expressions and an environment,
  -- if canSolve returns true, produce a subset proof
  solve′ : ∀ (e₁ e₂ : Expr) (ρ : Env)
         → {pf : canSolve (flatten e₁) (flatten e₂) ≡ true}
         → ⟦ e₁ ⟧ ρ ⊆ ⟦ e₂ ⟧ ρ
  solve′ e₁ e₂ ρ {pf} y yIn =
    let -- Convert membership through flatten-correct
        nf₁ = flatten e₁
        nf₂ = flatten e₂
        
        -- y ∈ ⟦ e₁ ⟧ ρ implies y ∈ ⟦ nf₁ ⟧nf ρ (via flatten-correct)
        yInNf₁ : y ∈ ⟦ nf₁ ⟧nf ρ
        yInNf₁ = subst (y ∈_) (sym (flatten-correct e₁ ρ)) yIn
        
        -- Use solveNF to route to RHS
        yInNf₂ : y ∈ ⟦ nf₂ ⟧nf ρ
        yInNf₂ = solveNF nf₁ nf₂ ρ pf y yInNf₁
        
    in subst (y ∈_) (flatten-correct e₂ ρ) yInNf₂

  solve : ∀ (e₁ e₂ : Expr) (ρ : Env)
        → {pf : canSolve (flatten e₁) (flatten e₂) ≡ true}
        → ⟦ e₁ ⟧ ρ ⊆ᵢ ⟦ e₂ ⟧ ρ
  solve e₁ e₂ ρ {pf} {y} yIn = solve′ e₁ e₂ ρ {pf} y yIn

  -- Split-rem lemma: Γ ⊆ [A] ++ (Γ - A)
  -- This is the key pattern the decision procedure (canSolve) cannot handle,
  -- because it requires 1-to-many atom routing.
  -- Defined directly on lists/removeAll rather than through the DSL, avoiding
  -- with-abstraction mismatch issues with ⟦_⟧.
  elem-or-removeAll′ : ∀ (x : A) (xs : List A)
    → xs ⊆ ((x ∷ []) ++ removeAll x xs)
  elem-or-removeAll′ x xs y yIn with x ≟ y
  ... | yes eq = subst (λ z → y ∈ (z ∷ removeAll x xs)) (sym eq) (hereA refl)
  ... | no neq = thereA (mem-removeAll-neq yIn neq)

  elem-or-removeAll : ∀ (x : A) (xs : List A)
    → xs ⊆ᵢ ((x ∷ []) ++ removeAll x xs)
  elem-or-removeAll x xs {y} yIn = elem-or-removeAll′ x xs y yIn

  -- Dual: Γ ⊆ (Γ - A) ++ [A]
  removeAll-or-elem′ : ∀ (x : A) (xs : List A)
    → xs ⊆ (removeAll x xs ++ (x ∷ []))
  removeAll-or-elem′ x xs y yIn with x ≟ y
  ... | yes eq = ∈-++⁺ʳ (removeAll x xs) (subst (λ z → y ∈ (z ∷ [])) (sym eq) (hereA refl))
  ... | no neq = ∈-++⁺ˡ (mem-removeAll-neq yIn neq)

  removeAll-or-elem : ∀ (x : A) (xs : List A)
    → xs ⊆ᵢ (removeAll x xs ++ (x ∷ []))
  removeAll-or-elem x xs {y} yIn = removeAll-or-elem′ x xs y yIn
