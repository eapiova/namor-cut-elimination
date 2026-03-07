{-# OPTIONS --safe #-}
module NAMOR.List.Membership where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List.Base
open import NAMOR.List.Any
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

private variable
  ℓ ℓ' : Level
  A : Type ℓ
  B : Type ℓ'

_∈_ : {A : Type ℓ} → A → List A → Type ℓ
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Type ℓ} → A → List A → Type ℓ
x ∉ xs = ¬ (x ∈ xs)

_⊆_ : {A : Type ℓ} → List A → List A → Type ℓ
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

infix 4 _∈_ _∉_ _⊆_

∈-++⁺ˡ : {x : A} {xs ys : List A}
  → x ∈ xs → x ∈ (xs ++ ys)
∈-++⁺ˡ = Any-++⁺ˡ

∈-++⁺ʳ : {x : A} (xs : List A) {ys : List A}
  → x ∈ ys → x ∈ (xs ++ ys)
∈-++⁺ʳ = Any-++⁺ʳ

∈-++⁻ : {x : A} (xs : List A) {ys : List A}
  → x ∈ (xs ++ ys) → (x ∈ xs) ⊎ (x ∈ ys)
∈-++⁻ = Any-++⁻

∈-map⁺ : {f : A → B} {x : A} {xs : List A}
  → x ∈ xs → f x ∈ map f xs
∈-map⁺ (here p)  = here (cong _ p)
∈-map⁺ (there m) = there (∈-map⁺ m)

∈-map⁻ : {f : A → B} {y : B} {xs : List A}
  → y ∈ map f xs
  → Σ _ λ x → (x ∈ xs) × (y ≡ f x)
∈-map⁻ {xs = x ∷ _}  (here p)  = x , here refl , p
∈-map⁻ {xs = _ ∷ xs} (there m) =
  let (x' , m' , eq) = ∈-map⁻ m
  in x' , there m' , eq

∈-here : {x : A} {xs : List A} → x ∈ (x ∷ xs)
∈-here = here refl
