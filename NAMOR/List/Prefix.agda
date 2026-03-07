{-# OPTIONS --safe #-}
module NAMOR.List.Prefix where
open import Cubical.Foundations.Prelude
open import Cubical.Data.List.Base
open import Cubical.Data.List.Properties using (++-assoc)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary

private variable
  ℓ ℓ' ℓr : Level
  A : Type ℓ
  B : Type ℓ'

-- Heterogeneous prefix, parameterized by a relation R
-- Port of Data.List.Relation.Binary.Prefix.Heterogeneous
data Prefix {A : Type ℓ} {B : Type ℓ'}
  (R : A → B → Type ℓr)
  : List A → List B → Type (ℓ-max (ℓ-max ℓ ℓ') ℓr) where
  []  : ∀ {bs} → Prefix R [] bs
  _∷_ : ∀ {a b as bs}
    → R a b → Prefix R as bs → Prefix R (a ∷ as) (b ∷ bs)

-- Homogeneous prefix with path equality
_⊑_ : {A : Type ℓ} → List A → List A → Type ℓ
_⊑_ = Prefix _≡_

infix 4 _⊑_

-- Basic properties
⊑-refl : (xs : List A) → xs ⊑ xs
⊑-refl []       = []
⊑-refl (x ∷ xs) = refl ∷ ⊑-refl xs

⊑-trans : {xs ys zs : List A}
  → xs ⊑ ys → ys ⊑ zs → xs ⊑ zs
⊑-trans []       _        = []
⊑-trans (p ∷ ps) (q ∷ qs) = (p ∙ q) ∷ ⊑-trans ps qs

⊑-nil : {xs : List A} → [] ⊑ xs
⊑-nil = []

-- Strict prefix
_⊂_ : {A : Type ℓ} → List A → List A → Type ℓ
xs ⊂ ys = (xs ⊑ ys) × (¬ (xs ≡ ys))

infix 4 _⊂_

-- Prefix via concatenation
prefixConcat : (xs ys : List A) → xs ⊑ (xs ++ ys)
prefixConcat []       ys = []
prefixConcat (x ∷ xs) ys = refl ∷ prefixConcat xs ys

⊑-++ = prefixConcat

-- Suffix extraction
suffix : {xs ys : List A} → xs ⊑ ys → List A
suffix {ys = ys} [] = ys
suffix {ys = _ ∷ _} (_ ∷ p) = suffix p

removePrefix = suffix

-- Suffix correctness: xs ++ suffix p ≡ ys
suffix-correct : {xs ys : List A}
  → (p : xs ⊑ ys)
  → xs ++ suffix p ≡ ys
suffix-correct {xs = []}     []      = refl
suffix-correct {xs = x ∷ xs} (q ∷ p) =
  cong₂ _∷_ q (suffix-correct p)

removePrefixPf = suffix-correct

-- Decidable prefix (given decidable equality)
⊑-dec : Discrete A
  → (xs ys : List A) → Dec (xs ⊑ ys)
⊑-dec _≟_ [] ys = yes []
⊑-dec _≟_ (x ∷ xs) [] = no λ ()
⊑-dec _≟_ (x ∷ xs) (y ∷ ys) with x ≟ y
... | no ¬p = no λ where (p ∷ _) → ¬p p
... | yes p with ⊑-dec _≟_ xs ys
... | yes q = yes (p ∷ q)
... | no ¬q = no λ where (_ ∷ q) → ¬q q
