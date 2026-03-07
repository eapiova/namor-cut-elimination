{-# OPTIONS --safe #-}

module NAMOR.List.RemoveAll where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List.Base using (List; []; _∷_; _++_)
open import Cubical.Relation.Nullary
  using (Dec; Discrete; yes; no; ¬_)
open import Cubical.Data.Empty as ⊥ using (⊥) renaming (rec to ⊥-rec)
open import NAMOR.List.Any using (here; there)
open import NAMOR.List.Membership using (_∈_; _⊆_)

module RemoveAll {ℓ} {A : Type ℓ} (_≟_ : Discrete A) where

  _≢_ : A → A → Type ℓ
  x ≢ y = ¬ (x ≡ y)

  removeAll : A → List A → List A
  removeAll x [] = []
  removeAll x (y ∷ ys) with x ≟ y
  ... | yes _ = removeAll x ys
  ... | no _ = y ∷ removeAll x ys

  mem-removeAll-subset : ∀ {x : A} {xs : List A} {y : A}
    → y ∈ removeAll x xs → y ∈ xs
  mem-removeAll-subset {x} {[]} ()
  mem-removeAll-subset {x} {z ∷ xs} yIn with x ≟ z
  ... | yes _ = there (mem-removeAll-subset yIn)
  ... | no _ with yIn
  ...   | here p = here p
  ...   | there yIn' = there (mem-removeAll-subset yIn')

  mem-removeAll-neq : ∀ {x y : A} {xs : List A}
    → y ∈ xs → x ≢ y → y ∈ removeAll x xs
  mem-removeAll-neq {x} {y} {[]} () neq
  mem-removeAll-neq {x} {y} {z ∷ xs} (here y≡z) neq with x ≟ z
  ... | yes x≡z = ⊥-rec (neq (x≡z ∙ sym y≡z))
  ... | no _ = here y≡z
  mem-removeAll-neq {x} {y} {z ∷ xs} (there yIn) neq with x ≟ z
  ... | yes _ = mem-removeAll-neq yIn neq
  ... | no _ = there (mem-removeAll-neq yIn neq)

  not-in-removeAll : ∀ (x : A) (xs : List A) → x ∈ removeAll x xs → ⊥
  not-in-removeAll x [] ()
  not-in-removeAll x (z ∷ xs) xIn with x ≟ z
  ... | yes _ = not-in-removeAll x xs xIn
  ... | no neq with xIn
  ...   | here p = neq p
  ...   | there xIn' = not-in-removeAll x xs xIn'

  removeAll-++ : ∀ (x : A) (xs ys : List A)
    → removeAll x (xs ++ ys) ≡ removeAll x xs ++ removeAll x ys
  removeAll-++ x [] ys = refl
  removeAll-++ x (z ∷ xs) ys with x ≟ z
  ... | yes _ = removeAll-++ x xs ys
  ... | no _ = cong (z ∷_) (removeAll-++ x xs ys)

  subset-removeAll-mono : ∀ {xs ys : List A} (x : A)
    → xs ⊆ ys → removeAll x xs ⊆ removeAll x ys
  subset-removeAll-mono {xs} {ys} x sub {y} yIn =
    keep (x ≟ y)
    where
      yInXs : y ∈ xs
      yInXs = mem-removeAll-subset yIn

      yInYs : y ∈ ys
      yInYs = sub yInXs

      keep : Dec (x ≡ y) → y ∈ removeAll x ys
      keep (yes p) =
        ⊥-rec
          (not-in-removeAll x xs
            (subst (_∈ removeAll x xs) (sym p) yIn))
      keep (no neq) = mem-removeAll-neq yInYs neq

  private
    removeAll-yes : ∀ (x z : A) (zs : List A)
      → x ≡ z → removeAll x (z ∷ zs) ≡ removeAll x zs
    removeAll-yes x z zs eq with x ≟ z
    ... | yes _ = refl
    ... | no neq = ⊥-rec (neq eq)

    removeAll-no : ∀ (x z : A) (zs : List A)
      → x ≢ z → removeAll x (z ∷ zs) ≡ z ∷ removeAll x zs
    removeAll-no x z zs neq with x ≟ z
    ... | yes eq = ⊥-rec (neq eq)
    ... | no _ = refl

    removeAll-comm-aux : ∀ (x y z : A) (zs : List A)
      → removeAll x (removeAll y zs) ≡ removeAll y (removeAll x zs)
      → Dec (y ≡ z) → Dec (x ≡ z)
      → removeAll x (removeAll y (z ∷ zs)) ≡ removeAll y (removeAll x (z ∷ zs))
    removeAll-comm-aux x y z zs ih (yes yeq) (yes xeq) =
      cong (removeAll x) (removeAll-yes y z zs yeq)
      ∙ ih
      ∙ sym (cong (removeAll y) (removeAll-yes x z zs xeq))
    removeAll-comm-aux x y z zs ih (yes yeq) (no xneq) =
      cong (removeAll x) (removeAll-yes y z zs yeq)
      ∙ ih
      ∙ sym (removeAll-yes y z (removeAll x zs) yeq)
      ∙ sym (cong (removeAll y) (removeAll-no x z zs xneq))
    removeAll-comm-aux x y z zs ih (no yneq) (yes xeq) =
      cong (removeAll x) (removeAll-no y z zs yneq)
      ∙ removeAll-yes x z (removeAll y zs) xeq
      ∙ ih
      ∙ sym (cong (removeAll y) (removeAll-yes x z zs xeq))
    removeAll-comm-aux x y z zs ih (no yneq) (no xneq) =
      cong (removeAll x) (removeAll-no y z zs yneq)
      ∙ removeAll-no x z (removeAll y zs) xneq
      ∙ cong (z ∷_) ih
      ∙ sym (removeAll-no y z (removeAll x zs) yneq)
      ∙ sym (cong (removeAll y) (removeAll-no x z zs xneq))

  removeAll-comm : ∀ (x y : A) (zs : List A)
    → removeAll x (removeAll y zs) ≡ removeAll y (removeAll x zs)
  removeAll-comm x y [] = refl
  removeAll-comm x y (z ∷ zs) =
    removeAll-comm-aux x y z zs (removeAll-comm x y zs) (y ≟ z) (x ≟ z)
