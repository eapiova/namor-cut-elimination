{-# OPTIONS --safe #-}

-- Generalized structural rules for E_pos.
-- Bring-to-front, put-back, weakening, subset weakening.
-- Adapts S4dot2/System.agda:246-483.
-- (OVERLAY25 paper, Section 4)

open import NAMOR.Final.Syntax using (Logic)

module NAMOR.Final.Structural (M : Logic) where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List
open import Cubical.Data.List.Properties using (++-assoc; ++-unit-r)
open import NAMOR.List.Any
  using (Any; here; there; any?)
open import NAMOR.List.Membership
  using (_∈_; _⊆_; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-here)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary

open import NAMOR.Final.Syntax hiding (Logic; Not)
open import NAMOR.Final.System M
open import NAMOR.Final.InitLemmas
  using (remove-first; remove-first-++-l; remove-first-++-r;
         mem-remove-first)

------------------------------------------------------------------------
-- Decidable membership for PFormula

_∈?_ : (x : PFormula) (xs : Ctx) → Dec (x ∈ xs)
x ∈? xs = any? (x ≟pf_) xs

------------------------------------------------------------------------
-- Bring to front (Left)

bring-to-front-ctx : ∀ {Δ} (Γ₁ Γ₂ : Ctx) (x : PFormula) (p : x ∈ Γ₂)
  → (Γ₁ ++ Γ₂) ⊢ Δ
  → (Γ₁ ++ x ∷ remove-first x Γ₂ p) ⊢ Δ
bring-to-front-ctx {Δ} Γ₁ _ x (here {xs = xs} eq) d =
  subst (λ z → (Γ₁ ++ z ∷ xs) ⊢ Δ) (sym eq) d
bring-to-front-ctx {Δ} Γ₁ _
  x (there {x = y} {xs = Γ₂} p) d =
  let
    -- d : (Γ₁ ++ y ∷ Γ₂) ⊢ Δ
    -- Reassociate to (Γ₁ ++ [y]) ++ Γ₂
    d' = subst (_⊢ Δ) (sym (++-assoc Γ₁ [ y ] Γ₂)) d
    -- Recurse: bring x to front of Γ₂
    -- step1 : ((Γ₁ ++ [y]) ++ x ∷ rest) ⊢ Δ
    step1 = bring-to-front-ctx (Γ₁ ++ [ y ]) Γ₂ x p d'
    -- Reassociate to Γ₁ ++ y ∷ x ∷ rest
    step1' = subst (_⊢ Δ)
      (++-assoc Γ₁ [ y ] (x ∷ remove-first x Γ₂ p))
      step1
    -- Exchange y and x
    step2 = ExchangeL {Γ₁ = Γ₁}
      {Γ₂ = remove-first x Γ₂ p} step1'
    -- step2 : (Γ₁ ++ x ∷ y ∷ rest) ⊢ Δ — done!
  in step2

bring-to-front : ∀ {Δ} (Γ : Ctx) (x : PFormula) (p : x ∈ Γ)
  → (Γ ⊢ Δ) → (x ∷ remove-first x Γ p ⊢ Δ)
bring-to-front Γ x p d = bring-to-front-ctx [] Γ x p d

------------------------------------------------------------------------
-- Bring to front (Right)

bring-to-front-ctx-r : ∀ {Γ} (Δ₁ Δ₂ : Ctx) (x : PFormula) (p : x ∈ Δ₂)
  → (Γ ⊢ Δ₁ ++ Δ₂)
  → (Γ ⊢ Δ₁ ++ x ∷ remove-first x Δ₂ p)
bring-to-front-ctx-r {Γ} Δ₁ _ x (here {xs = xs} eq) d =
  subst (λ z → Γ ⊢ Δ₁ ++ z ∷ xs) (sym eq) d
bring-to-front-ctx-r {Γ} Δ₁ _
  x (there {x = y} {xs = Δ₂} p) d =
  let
    d' = subst (Γ ⊢_) (sym (++-assoc Δ₁ [ y ] Δ₂)) d
    step1 = bring-to-front-ctx-r (Δ₁ ++ [ y ]) Δ₂ x p d'
    step1' = subst (Γ ⊢_)
      (++-assoc Δ₁ [ y ] (x ∷ remove-first x Δ₂ p))
      step1
    step2 = ExchangeR {Δ₁ = Δ₁}
      {Δ₂ = remove-first x Δ₂ p} step1'
  in step2

bring-to-front-r : ∀ {Γ} (Δ : Ctx) (x : PFormula) (p : x ∈ Δ)
  → (Γ ⊢ Δ) → (Γ ⊢ x ∷ remove-first x Δ p)
bring-to-front-r Δ x p d = bring-to-front-ctx-r [] Δ x p d

------------------------------------------------------------------------
-- Put back (Left) — inverse of bring-to-front

put-back-ctx : ∀ {Δ} (Γ₁ Γ₂ : Ctx) (x : PFormula) (p : x ∈ Γ₂)
  → (Γ₁ ++ x ∷ remove-first x Γ₂ p) ⊢ Δ
  → (Γ₁ ++ Γ₂) ⊢ Δ
put-back-ctx {Δ} Γ₁ _ x (here {xs = xs} eq) d =
  subst (λ z → (Γ₁ ++ z ∷ xs) ⊢ Δ) eq d
put-back-ctx {Δ} Γ₁ _
  x (there {x = y} {xs = Γ₂} p) d =
  let
    -- d : (Γ₁ ++ x ∷ y ∷ rest) ⊢ Δ
    -- Exchange x and y back
    step1 = ExchangeL {Γ₁ = Γ₁}
      {Γ₂ = remove-first x Γ₂ p} d
    -- step1 : (Γ₁ ++ y ∷ x ∷ rest) ⊢ Δ
    -- Reassociate to (Γ₁ ++ [y]) ++ x ∷ rest
    step1' = subst (_⊢ Δ)
      (sym (++-assoc Γ₁ [ y ]
        (x ∷ remove-first x Γ₂ p)))
      step1
    -- Recurse to put x back in Γ₂
    res = put-back-ctx (Γ₁ ++ [ y ]) Γ₂ x p step1'
  in subst (_⊢ Δ) (++-assoc Γ₁ [ y ] Γ₂) res

put-back : ∀ {Δ} (Γ : Ctx) (x : PFormula) (p : x ∈ Γ)
  → (x ∷ remove-first x Γ p) ⊢ Δ → (Γ ⊢ Δ)
put-back Γ x p d = put-back-ctx [] Γ x p d

------------------------------------------------------------------------
-- Put back (Right)

put-back-ctx-r : ∀ {Γ} (Δ₁ Δ₂ : Ctx) (x : PFormula) (p : x ∈ Δ₂)
  → (Γ ⊢ Δ₁ ++ x ∷ remove-first x Δ₂ p)
  → (Γ ⊢ Δ₁ ++ Δ₂)
put-back-ctx-r {Γ} Δ₁ _ x (here {xs = xs} eq) d =
  subst (λ z → Γ ⊢ Δ₁ ++ z ∷ xs) eq d
put-back-ctx-r {Γ} Δ₁ _
  x (there {x = y} {xs = Δ₂} p) d =
  let
    step1 = ExchangeR {Δ₁ = Δ₁}
      {Δ₂ = remove-first x Δ₂ p} d
    step1' = subst (Γ ⊢_)
      (sym (++-assoc Δ₁ [ y ]
        (x ∷ remove-first x Δ₂ p)))
      step1
    res = put-back-ctx-r (Δ₁ ++ [ y ]) Δ₂ x p step1'
  in subst (Γ ⊢_) (++-assoc Δ₁ [ y ] Δ₂) res

put-back-r : ∀ {Γ} (Δ : Ctx) (x : PFormula) (p : x ∈ Δ)
  → (Γ ⊢ x ∷ remove-first x Δ p) → (Γ ⊢ Δ)
put-back-r Δ x p d = put-back-ctx-r [] Δ x p d

------------------------------------------------------------------------
-- Generalized weakening

weakening-left : ∀ {Γ Δ} (Σ : Ctx) → Γ ⊢ Δ → (Σ ++ Γ) ⊢ Δ
weakening-left []      d = d
weakening-left (x ∷ Σ) d = WeakenL (weakening-left Σ d)

weakening-right : ∀ {Γ Δ} (Σ : Ctx) → Γ ⊢ Δ → Γ ⊢ (Σ ++ Δ)
weakening-right []      d = d
weakening-right (x ∷ Σ) d = WeakenR (weakening-right Σ d)

------------------------------------------------------------------------
-- Bring last to front (Left) — for use with subset weakening

bring-last-to-front : ∀ {Δ} (Γ : Ctx) (x : PFormula)
  → (Γ ++ [ x ]) ⊢ Δ → (x ∷ Γ) ⊢ Δ
bring-last-to-front {Δ} Γ x d =
  let
    p : x ∈ (Γ ++ [ x ])
    p = ∈-++⁺ʳ Γ ∈-here

    step1 = bring-to-front (Γ ++ [ x ]) x p d

    lem : remove-first x (Γ ++ [ x ]) p ≡ Γ
    lem = remove-first-++-r x Γ [ x ] ∈-here
        ∙ ++-unit-r Γ
  in subst (λ G → x ∷ G ⊢ Δ) lem step1

bring-last-to-front-r : ∀ {Γ} (Δ : Ctx) (x : PFormula)
  → (Γ ⊢ Δ ++ [ x ]) → (Γ ⊢ x ∷ Δ)
bring-last-to-front-r {Γ} Δ x d =
  let
    p : x ∈ (Δ ++ [ x ])
    p = ∈-++⁺ʳ Δ ∈-here

    step1 = bring-to-front-r (Δ ++ [ x ]) x p d

    lem : remove-first x (Δ ++ [ x ]) p ≡ Δ
    lem = remove-first-++-r x Δ [ x ] ∈-here
        ∙ ++-unit-r Δ
  in subst (λ D → Γ ⊢ x ∷ D) lem step1

------------------------------------------------------------------------
-- Subset weakening (Left)

subset-weakening-left-gen : ∀ {Γ Γ' Σ Δ}
  → Γ ⊆ Γ' → (Γ ++ Σ) ⊢ Δ → (Γ' ++ Σ) ⊢ Δ
subset-weakening-left-gen {[]} {Γ'} sub d =
  weakening-left Γ' d
subset-weakening-left-gen {x ∷ Γ} {Γ'} {Σ} {Δ} sub d
  with x ∈? Γ
... | yes xInΓ =
  let
    -- x appears in Γ, so contract it out
    d' : x ∷ x ∷ remove-first x (Γ ++ Σ) (∈-++⁺ˡ xInΓ) ⊢ Δ
    d' = bring-to-front-ctx [ x ] (Γ ++ Σ) x
           (∈-++⁺ˡ xInΓ) d

    d'' : x ∷ remove-first x (Γ ++ Σ) (∈-++⁺ˡ xInΓ) ⊢ Δ
    d'' = ContractL d'

    d-back = put-back (Γ ++ Σ) x (∈-++⁺ˡ xInΓ) d''

    sub' : Γ ⊆ Γ'
    sub' yIn = sub (there yIn)
  in subset-weakening-left-gen sub' d-back

... | no xNotInΓ =
  let
    xInΓ' : x ∈ Γ'
    xInΓ' = sub ∈-here

    gammaSub : Γ ⊆ remove-first x Γ' xInΓ'
    gammaSub {y} yIn =
      let
        yInΓ' = sub (there yIn)
        neq : ¬ (x ≡ y)
        neq p = xNotInΓ (subst (_∈ Γ) (sym p) yIn)
      in mem-remove-first x Γ' xInΓ' y yInΓ' neq

    -- Move x from head of (x ∷ Γ ++ Σ) into Σ position
    d-perm : (Γ ++ x ∷ Σ) ⊢ Δ
    d-perm = put-back (Γ ++ x ∷ Σ) x (∈-++⁺ʳ Γ ∈-here)
      (subst (λ G → x ∷ G ⊢ Δ)
        (sym (remove-first-++-r x Γ (x ∷ Σ) ∈-here)) d)

    -- Apply IH
    ih : (remove-first x Γ' xInΓ') ++ (x ∷ Σ) ⊢ Δ
    ih = subset-weakening-left-gen gammaSub d-perm

    -- Bring x back to front
    d-front = bring-to-front
      ((remove-first x Γ' xInΓ') ++ x ∷ Σ) x
      (∈-++⁺ʳ _ ∈-here) ih

    d-front' : x ∷ (remove-first x Γ' xInΓ') ++ Σ ⊢ Δ
    d-front' = subst (λ G → x ∷ G ⊢ Δ)
      (remove-first-++-r x
        (remove-first x Γ' xInΓ') (x ∷ Σ) ∈-here)
      d-front

    -- Put x back into Γ'
    res : (Γ' ++ Σ) ⊢ Δ
    res = put-back (Γ' ++ Σ) x (∈-++⁺ˡ xInΓ')
      (subst (λ G → x ∷ G ⊢ Δ)
        (sym (remove-first-++-l x Γ' Σ xInΓ'))
        d-front')
  in res

------------------------------------------------------------------------
-- Subset weakening (Right)

subset-weakening-right-gen : ∀ {Δ Δ' Σ Γ}
  → Δ ⊆ Δ' → (Γ ⊢ Δ ++ Σ) → (Γ ⊢ Δ' ++ Σ)
subset-weakening-right-gen {[]} {Δ'} sub d =
  weakening-right Δ' d
subset-weakening-right-gen {x ∷ Δ} {Δ'} {Σ} {Γ} sub d
  with x ∈? Δ
... | yes xInΔ =
  let
    d' = bring-to-front-ctx-r [ x ] (Δ ++ Σ) x
           (∈-++⁺ˡ xInΔ) d
    d'' = ContractR d'
    d-back = put-back-r (Δ ++ Σ) x (∈-++⁺ˡ xInΔ) d''

    sub' : Δ ⊆ Δ'
    sub' yIn = sub (there yIn)
  in subset-weakening-right-gen sub' d-back

... | no xNotInΔ =
  let
    xInΔ' = sub ∈-here

    deltaSub : Δ ⊆ remove-first x Δ' xInΔ'
    deltaSub {y} yIn =
      mem-remove-first x Δ' xInΔ' y
        (sub (there yIn))
        (λ p → xNotInΔ (subst (_∈ Δ) (sym p) yIn))

    d-perm : Γ ⊢ (Δ ++ x ∷ Σ)
    d-perm = put-back-r (Δ ++ x ∷ Σ) x (∈-++⁺ʳ Δ ∈-here)
      (subst (λ D → Γ ⊢ x ∷ D)
        (sym (remove-first-++-r x Δ (x ∷ Σ) ∈-here)) d)

    ih = subset-weakening-right-gen deltaSub d-perm

    d-front = bring-to-front-r
      ((remove-first x Δ' xInΔ') ++ x ∷ Σ) x
      (∈-++⁺ʳ _ ∈-here) ih

    d-front' : Γ ⊢ x ∷ (remove-first x Δ' xInΔ') ++ Σ
    d-front' = subst (λ D → Γ ⊢ x ∷ D)
      (remove-first-++-r x
        (remove-first x Δ' xInΔ') (x ∷ Σ) ∈-here)
      d-front

    res = put-back-r (Δ' ++ Σ) x (∈-++⁺ˡ xInΔ')
      (subst (λ D → Γ ⊢ x ∷ D)
        (sym (remove-first-++-l x Δ' Σ xInΔ'))
        d-front')
  in res

------------------------------------------------------------------------
-- Full structural rule

structural : ∀ {Γ Δ Γ' Δ'} → Γ ⊆ Γ' → Δ ⊆ Δ'
  → (Γ ⊢ Δ) → (Γ' ⊢ Δ')
structural {Γ} {Δ} {Γ'} {Δ'} subG subD d =
  let
    step1 = subset-weakening-left-gen {Σ = []} subG
      (subst (_⊢ Δ) (sym (++-unit-r Γ)) d)
    step1' = subst (_⊢ Δ) (++-unit-r Γ') step1
    step2 = subset-weakening-right-gen {Σ = []} subD
      (subst (Γ' ⊢_) (sym (++-unit-r Δ)) step1')
  in subst (Γ' ⊢_) (++-unit-r Δ') step2
