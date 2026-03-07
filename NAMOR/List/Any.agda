{-# OPTIONS --safe #-}
module NAMOR.List.Any where
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary

private variable
  ℓ ℓ' ℓ'' : Level
  A : Type ℓ
  B : Type ℓ'

data Any {A : Type ℓ} (P : A → Type ℓ') : List A → Type (ℓ-max ℓ ℓ') where
  here  : ∀ {x xs} → P x → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

data All {A : Type ℓ} (P : A → Type ℓ') : List A → Type (ℓ-max ℓ ℓ') where
  []  : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

infixr 5 _∷_

module _ {P : A → Type ℓ'} where
  ¬Any[] : ¬ Any P []
  ¬Any[] ()

  toSum : ∀ {x : A} {xs} → Any P (x ∷ xs) → P x ⊎ Any P xs
  toSum (here px)  = inl px
  toSum (there pxs) = inr pxs

  fromSum : ∀ {x : A} {xs} → P x ⊎ Any P xs → Any P (x ∷ xs)
  fromSum (inl px)  = here px
  fromSum (inr pxs) = there pxs

  map-Any : ∀ {Q : A → Type ℓ''}
    → (∀ {x} → P x → Q x)
    → ∀ {xs} → Any P xs → Any Q xs
  map-Any f (here px)   = here (f px)
  map-Any f (there pxs) = there (map-Any f pxs)

  any? : (∀ x → Dec (P x))
    → ∀ (xs : List A) → Dec (Any P xs)
  any? p? [] = no ¬Any[]
  any? p? (x ∷ xs) with p? x
  ... | yes px = yes (here px)
  ... | no ¬px with any? p? xs
  ... | yes pxs = yes (there pxs)
  ... | no ¬pxs = no λ where
    (here px) → ¬px px
    (there pxs) → ¬pxs pxs

module _ {P : A → Type ℓ'} where
  All-head : ∀ {x : A} {xs} → All P (x ∷ xs) → P x
  All-head (px ∷ _) = px

  All-tail : ∀ {x : A} {xs} → All P (x ∷ xs) → All P xs
  All-tail (_ ∷ pxs) = pxs

  map-All : ∀ {Q : A → Type ℓ''}
    → (∀ {x} → P x → Q x)
    → ∀ {xs} → All P xs → All Q xs
  map-All f [] = []
  map-All f (px ∷ pxs) = f px ∷ map-All f pxs

  all? : (∀ x → Dec (P x))
    → ∀ (xs : List A) → Dec (All P xs)
  all? p? [] = yes []
  all? p? (x ∷ xs) with p? x
  ... | no ¬px = no λ pxxs → ¬px (All-head pxxs)
  ... | yes px with all? p? xs
  ... | yes pxs = yes (px ∷ pxs)
  ... | no ¬pxs = no λ pxxs → ¬pxs (All-tail pxxs)

module _ {P : A → Type ℓ'} where
  Any-++⁺ˡ : ∀ {xs ys : List A}
    → Any P xs → Any P (xs ++ ys)
  Any-++⁺ˡ (here px)   = here px
  Any-++⁺ˡ (there pxs) = there (Any-++⁺ˡ pxs)

  Any-++⁺ʳ : ∀ (xs : List A) {ys}
    → Any P ys → Any P (xs ++ ys)
  Any-++⁺ʳ []       pys = pys
  Any-++⁺ʳ (_ ∷ xs) pys = there (Any-++⁺ʳ xs pys)

  Any-++⁻ : ∀ (xs : List A) {ys}
    → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  Any-++⁻ []       pys       = inr pys
  Any-++⁻ (_ ∷ xs) (here px) = inl (here px)
  Any-++⁻ (_ ∷ xs) (there p) with Any-++⁻ xs p
  ... | inl pxs = inl (there pxs)
  ... | inr pys = inr pys

module _ {P : A → Type ℓ'} where
  All-++⁺ : ∀ {xs ys : List A}
    → All P xs → All P ys → All P (xs ++ ys)
  All-++⁺ []         pys = pys
  All-++⁺ (px ∷ pxs) pys = px ∷ All-++⁺ pxs pys

  All-++⁻ˡ : ∀ (xs : List A) {ys}
    → All P (xs ++ ys) → All P xs
  All-++⁻ˡ []       _           = []
  All-++⁻ˡ (_ ∷ xs) (px ∷ pxs) = px ∷ All-++⁻ˡ xs pxs

  All-++⁻ʳ : ∀ (xs : List A) {ys}
    → All P (xs ++ ys) → All P ys
  All-++⁻ʳ []       pys         = pys
  All-++⁻ʳ (_ ∷ xs) (_ ∷ pxys) = All-++⁻ʳ xs pxys

Any-map⁺ : ∀ {P : B → Type ℓ''} {f : A → B}
  {xs : List A}
  → Any (P ∘ f) xs → Any P (map f xs)
Any-map⁺ (here px)   = here px
Any-map⁺ (there pxs) = there (Any-map⁺ pxs)

Any-map⁻ : ∀ {P : B → Type ℓ''} {f : A → B}
  (xs : List A)
  → Any P (map f xs) → Any (P ∘ f) xs
Any-map⁻ (_ ∷ _)  (here px)   = here px
Any-map⁻ (_ ∷ xs) (there pxs) = there (Any-map⁻ xs pxs)
