{-# OPTIONS --safe #-}

module NAMOR.Solver.Subset.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty as Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Relation.Nullary using (Discrete; Dec; yes; no)

open import NAMOR.List.Any using (here; there)
open import NAMOR.List.Membership as Mem using (_∈_)
open import NAMOR.List.RemoveAll

private
  variable
    ℓ : Level

-- Inequality
_≢_ : ∀ {ℓ'} {A : Type ℓ'} → A → A → Type ℓ'
x ≢ y = x ≡ y → ⊥

_⊆_ : ∀ {ℓ'} {A : Type ℓ'} → List A → List A → Type ℓ'
xs ⊆ ys = ∀ x → x ∈ xs → x ∈ ys

infix 4 _⊆_

-- Core solver module parameterized by element type with decidable equality
module SubsetSolver {A : Type ℓ} (_≟_ : Discrete A) where

  module RA = RemoveAll _≟_

  -- Extract Bool from Dec.
  ⌊_⌋ : {P : Type ℓ} → Dec P → Bool
  ⌊ yes _ ⌋ = true
  ⌊ no _ ⌋ = false

  -- removeAll and core lemmas come from generic NAMOR.List.RemoveAll.
  removeAll : A → List A → List A
  removeAll = RA.removeAll

  mem-removeAll-subset : ∀ {x : A} {xs : List A} {y : A}
    → y ∈ removeAll x xs → y ∈ xs
  mem-removeAll-subset = RA.mem-removeAll-subset

  mem-removeAll-neq : ∀ {x y : A} {xs : List A}
    → y ∈ xs → x ≢ y → y ∈ removeAll x xs
  mem-removeAll-neq = RA.mem-removeAll-neq

  not-in-removeAll : ∀ (x : A) (xs : List A) → x ∈ removeAll x xs → ⊥
  not-in-removeAll = RA.not-in-removeAll

  removeAll-++ : ∀ (x : A) (xs ys : List A)
    → removeAll x (xs ++ ys) ≡ removeAll x xs ++ removeAll x ys
  removeAll-++ = RA.removeAll-++

  subset-removeAll-mono : ∀ {xs ys : List A} (x : A)
    → xs ⊆ ys → removeAll x xs ⊆ removeAll x ys
  subset-removeAll-mono {xs} {ys} x sub y yIn =
    RA.subset-removeAll-mono x sub' yIn
    where
      sub' : Mem._⊆_ xs ys
      sub' {z} zIn = sub z zIn

  -- Simple expression language.
  data Expr : Type ℓ where
    var   : ℕ → Expr
    []ₑ   : Expr
    elm   : ℕ → Expr
    _++ₑ_ : Expr → Expr → Expr
    rem   : Expr → ℕ → Expr

  infixr 5 _++ₑ_
  infixl 6 rem

  -- Environment: list vars and element vars.
  Env : Type ℓ
  Env = List (List A) × List A

  lookupList : List (List A) → ℕ → List A
  lookupList [] _ = []
  lookupList (x ∷ _) zero = x
  lookupList (_ ∷ xs) (suc n) = lookupList xs n

  lookupElem : List A → ℕ → Maybe A
  lookupElem [] _ = nothing
  lookupElem (x ∷ _) zero = just x
  lookupElem (_ ∷ xs) (suc n) = lookupElem xs n

  ⟦_⟧ : Expr → Env → List A
  ⟦ var i ⟧ (ρl , _) = lookupList ρl i
  ⟦ []ₑ ⟧ _ = []
  ⟦ elm i ⟧ (_ , ρe) with lookupElem ρe i
  ... | nothing = []
  ... | just x = x ∷ []
  ⟦ e₁ ++ₑ e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ ++ ⟦ e₂ ⟧ ρ
  ⟦ rem e i ⟧ (ρl , ρe) with lookupElem ρe i
  ... | nothing = ⟦ e ⟧ (ρl , ρe)
  ... | just x = removeAll x (⟦ e ⟧ (ρl , ρe))

  v : ℕ → Expr
  v = var
