{-# OPTIONS --safe #-}

-- Infrastructure lemmas for Init membership, has monotonicity,
-- modal/cut constraint weakening, and list removal.

module NAMOR.Final.InitLemmas where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List
open import Cubical.Data.List.Properties using (++-assoc; ++-unit-r)
open import NAMOR.List.Any
  using (Any; here; there; Any-++⁺ˡ; Any-++⁺ʳ; Any-++⁻)
open import NAMOR.List.Membership
  using (_∈_; _∉_; _⊆_; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-here)
open import NAMOR.List.Prefix
  using (_⊑_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary

open import NAMOR.Final.Syntax hiding (Not)

private variable
  ℓ : Level
  A : Type ℓ

------------------------------------------------------------------------
-- List removal: remove first occurrence via membership proof

remove-first : (x : A) (xs : List A) → x ∈ xs → List A
remove-first x (_ ∷ xs) (here _)  = xs
remove-first x (y ∷ xs) (there p) = y ∷ remove-first x xs p

remove-first-++-l : (x : A) (xs ys : List A) (p : x ∈ xs)
  → remove-first x (xs ++ ys) (∈-++⁺ˡ p)
  ≡ remove-first x xs p ++ ys
remove-first-++-l x (_ ∷ xs) ys (here _)  = refl
remove-first-++-l x (_ ∷ xs) ys (there p) =
  cong (_ ∷_) (remove-first-++-l x xs ys p)

remove-first-++-r : (x : A) (xs ys : List A) (p : x ∈ ys)
  → remove-first x (xs ++ ys) (∈-++⁺ʳ xs p)
  ≡ xs ++ remove-first x ys p
remove-first-++-r x []       ys p = refl
remove-first-++-r x (_ ∷ xs) ys p =
  cong (_ ∷_) (remove-first-++-r x xs ys p)

mem-remove-first : (x : A) (xs : List A) (p : x ∈ xs)
  (y : A) → y ∈ xs → ¬ (x ≡ y) → y ∈ remove-first x xs p
mem-remove-first x (_ ∷ xs) (here eq)  y (here ey) neq =
  ⊥.rec (neq (eq ∙ sym ey))
mem-remove-first x (_ ∷ xs) (here _)   y (there q) _ = q
mem-remove-first x (_ ∷ xs) (there p) y (here ey) neq =
  here ey
mem-remove-first x (_ ∷ xs) (there p) y (there q) neq =
  there (mem-remove-first x xs p y q neq)

------------------------------------------------------------------------
-- ∈Init lemmas

∈Init-∷ : ∀ {t Γ} (φ : PFormula)
  → t ∈Init Γ → t ∈Init (φ ∷ Γ)
∈Init-∷ φ (pf , m , p) = pf , there m , p

∈Init-here : ∀ {t Γ} (φ : PFormula)
  → t ⊑ PFormula.pos φ → t ∈Init (φ ∷ Γ)
∈Init-here φ p = φ , ∈-here , p

∈Init-++⁺ˡ : ∀ {t Γ Δ}
  → t ∈Init Γ → t ∈Init (Γ ++ Δ)
∈Init-++⁺ˡ (pf , m , p) = pf , ∈-++⁺ˡ m , p

∈Init-++⁺ʳ : ∀ {t} (Γ : Ctx) {Δ}
  → t ∈Init Δ → t ∈Init (Γ ++ Δ)
∈Init-++⁺ʳ Γ (pf , m , p) = pf , ∈-++⁺ʳ Γ m , p

∈Init-++⁻ : ∀ {t} (Γ : Ctx) {Δ}
  → t ∈Init (Γ ++ Δ) → (t ∈Init Γ) ⊎ (t ∈Init Δ)
∈Init-++⁻ Γ (pf , m , p) with ∈-++⁻ Γ m
... | inl mΓ = inl (pf , mΓ , p)
... | inr mΔ = inr (pf , mΔ , p)

∉Init-∷ : ∀ {t Γ} (φ : PFormula)
  → ¬ (t ⊑ PFormula.pos φ) → t ∉Init Γ → t ∉Init (φ ∷ Γ)
∉Init-∷ φ ¬p ¬m (pf , here eq , p) =
  ¬p (subst (_ ⊑_) (cong PFormula.pos eq) p)
∉Init-∷ φ ¬p ¬m (pf , there m , p) = ¬m (pf , m , p)

∉Init-++ : ∀ {t} (Γ Δ : Ctx)
  → t ∉Init Γ → t ∉Init Δ → t ∉Init (Γ ++ Δ)
∉Init-++ Γ Δ ¬Γ ¬Δ m with ∈Init-++⁻ Γ m
... | inl mΓ = ¬Γ mΓ
... | inr mΔ = ¬Δ mΔ

------------------------------------------------------------------------
-- has monotonicity

has-∷ : ∀ {Γ β} (φ : PFormula)
  → Γ has β → (φ ∷ Γ) has β
has-∷ φ = there

has-++⁺ˡ : ∀ {Γ Δ β}
  → Γ has β → (Γ ++ Δ) has β
has-++⁺ˡ = Any-++⁺ˡ

has-++⁺ʳ : ∀ (Γ : Ctx) {Δ β}
  → Δ has β → (Γ ++ Δ) has β
has-++⁺ʳ Γ h = Any-++⁺ʳ Γ h

------------------------------------------------------------------------
-- modalConstraint weakening
--
-- For S5/S4/S4.2/T/D/D4: constraint is position-only → identity.
-- For K/K4: constraint includes (Γ ++ Δ) has β → use has monotonicity.

modalConstraint-weaken-left : ∀ M {α β Γ Δ} (Γ' : Ctx)
  → modalConstraint M α β Γ Δ
  → modalConstraint M α β (Γ' ++ Γ) Δ
modalConstraint-weaken-left S5     Γ' c = tt
modalConstraint-weaken-left S4dot2 Γ' c = c
modalConstraint-weaken-left S4     Γ' c = c
modalConstraint-weaken-left T      Γ' c = c
modalConstraint-weaken-left D      Γ' c = c
modalConstraint-weaken-left D4     Γ' c = c
modalConstraint-weaken-left K4 {Γ = Γ} {Δ} Γ' (rel , h) =
  rel , subst (_has _)
    (sym (++-assoc Γ' Γ Δ)) (has-++⁺ʳ Γ' h)
modalConstraint-weaken-left K {Γ = Γ} {Δ} Γ' (rel , h) =
  rel , subst (_has _)
    (sym (++-assoc Γ' Γ Δ)) (has-++⁺ʳ Γ' h)

private
  has-weaken-right-++ : ∀ {β} (Γ Δ' Δ : Ctx)
    → (Γ ++ Δ) has β → (Γ ++ (Δ' ++ Δ)) has β
  has-weaken-right-++ Γ Δ' Δ h with Any-++⁻ Γ h
  ... | inl hΓ = has-++⁺ˡ hΓ
  ... | inr hΔ = has-++⁺ʳ Γ (has-++⁺ʳ Δ' hΔ)

modalConstraint-weaken-right : ∀ M {α β Γ Δ} (Δ' : Ctx)
  → modalConstraint M α β Γ Δ
  → modalConstraint M α β Γ (Δ' ++ Δ)
modalConstraint-weaken-right S5     Δ' c = tt
modalConstraint-weaken-right S4dot2 Δ' c = c
modalConstraint-weaken-right S4     Δ' c = c
modalConstraint-weaken-right T      Δ' c = c
modalConstraint-weaken-right D      Δ' c = c
modalConstraint-weaken-right D4     Δ' c = c
modalConstraint-weaken-right K4 {Γ = Γ} {Δ} Δ' (rel , h) =
  rel , has-weaken-right-++ Γ Δ' Δ h
modalConstraint-weaken-right K {Γ = Γ} {Δ} Δ' (rel , h) =
  rel , has-weaken-right-++ Γ Δ' Δ h
