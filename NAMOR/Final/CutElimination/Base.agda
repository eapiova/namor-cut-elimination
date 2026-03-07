{-# OPTIONS --safe #-}

open import NAMOR.Final.Syntax using (Logic)

module NAMOR.Final.CutElimination.Base (M : Logic) where

open import Cubical.Foundations.Prelude
  using (Type; _≡_; refl; sym; cong; cong₂; subst; J; substRefl; _∙_)
open import Cubical.Data.Empty renaming (rec to emptyRec; elim to ⊥-elim) using (⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.List using (List; _∷_; []; _++_; [_])
open import Cubical.Data.List.Properties using (++-assoc; ++-unit-r)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd; Σ)
open import Cubical.Relation.Nullary renaming (¬_ to Neg)
open import Cubical.Data.Unit using (Unit; tt)

open import NAMOR.List.Any using (here; there)
open import NAMOR.List.Membership
  using (_∈_; _⊆_; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-here)
open import NAMOR.Final.Syntax hiding (Logic)
open import NAMOR.Final.System M
open import NAMOR.Final.Structural M
open import NAMOR.Final.InitLemmas
  using (remove-first; remove-first-++-l; remove-first-++-r;
         mem-remove-first)
open import NAMOR.Final.CutElimination.Defs M public

------------------------------------------------------------------------
-- Transport preserves δ

subst-preserves-δ : ∀ {Γ Δ Δ'} (eq : Δ ≡ Δ') (p : Γ ⊢ Δ)
  → δ (subst (Γ ⊢_) eq p) ≡ δ p
subst-preserves-δ {Γ} {Δ} eq p =
  J (λ Δ' eq' → δ (subst (Γ ⊢_) eq' p) ≡ δ p)
    (cong δ (substRefl {B = Γ ⊢_} p))
    eq

subst-preserves-δ-ctx : ∀ {Γ Γ' Δ} (eq : Γ ≡ Γ') (p : Γ ⊢ Δ)
  → δ (subst (_⊢ Δ) eq p) ≡ δ p
subst-preserves-δ-ctx {Γ} {Δ = Δ} eq p =
  J (λ Γ' eq' → δ (subst (_⊢ Δ) eq' p) ≡ δ p)
    (cong δ (substRefl {B = _⊢ Δ} p))
    eq

------------------------------------------------------------------------
-- Structural helper preservation lemmas

bring-to-front-ctx-preserves-δ : ∀ {Δ} (Γ₁ Γ₂ : Ctx) (x : PFormula)
  (p : x ∈ Γ₂) (d : (Γ₁ ++ Γ₂) ⊢ Δ)
  → δ (bring-to-front-ctx Γ₁ Γ₂ x p d) ≡ δ d
bring-to-front-ctx-preserves-δ Γ₁ ._ x (here {xs = xs} eq) d =
  subst-preserves-δ-ctx (cong (λ z → Γ₁ ++ z ∷ xs) (sym eq)) d
bring-to-front-ctx-preserves-δ {Δ} Γ₁ ._ x
  (there {x = y} {xs = Γ₂} p) d =
  let
    d' = subst (_⊢ Δ) (sym (++-assoc Γ₁ [ y ] Γ₂)) d
    step1 = bring-to-front-ctx (Γ₁ ++ [ y ]) Γ₂ x p d'
    step1' = subst (_⊢ Δ)
      (++-assoc Γ₁ [ y ] (x ∷ remove-first x Γ₂ p))
      step1

    ih : δ step1 ≡ δ d'
    ih = bring-to-front-ctx-preserves-δ (Γ₁ ++ [ y ]) Γ₂ x p d'

    eq1 : δ d' ≡ δ d
    eq1 = subst-preserves-δ-ctx (sym (++-assoc Γ₁ [ y ] Γ₂)) d

    eq2 : δ step1' ≡ δ step1
    eq2 = subst-preserves-δ-ctx
      (++-assoc Γ₁ [ y ] (x ∷ remove-first x Γ₂ p))
      step1
  in eq2 ∙ ih ∙ eq1

bring-to-front-preserves-δ : ∀ {Δ} (Γ : Ctx) (x : PFormula)
  (p : x ∈ Γ) (d : Γ ⊢ Δ)
  → δ (bring-to-front Γ x p d) ≡ δ d
bring-to-front-preserves-δ Γ x p d =
  bring-to-front-ctx-preserves-δ [] Γ x p d

bring-to-front-ctx-r-preserves-δ : ∀ {Γ} (Δ₁ Δ₂ : Ctx) (x : PFormula)
  (p : x ∈ Δ₂) (d : Γ ⊢ (Δ₁ ++ Δ₂))
  → δ (bring-to-front-ctx-r Δ₁ Δ₂ x p d) ≡ δ d
bring-to-front-ctx-r-preserves-δ Δ₁ ._ x (here {xs = xs} eq) d =
  subst-preserves-δ (cong (λ z → Δ₁ ++ z ∷ xs) (sym eq)) d
bring-to-front-ctx-r-preserves-δ {Γ} Δ₁ ._ x
  (there {x = y} {xs = Δ₂} p) d =
  let
    d' = subst (Γ ⊢_) (sym (++-assoc Δ₁ [ y ] Δ₂)) d
    step1 = bring-to-front-ctx-r (Δ₁ ++ [ y ]) Δ₂ x p d'
    step1' = subst (Γ ⊢_)
      (++-assoc Δ₁ [ y ] (x ∷ remove-first x Δ₂ p))
      step1

    ih : δ step1 ≡ δ d'
    ih = bring-to-front-ctx-r-preserves-δ (Δ₁ ++ [ y ]) Δ₂ x p d'

    eq1 : δ d' ≡ δ d
    eq1 = subst-preserves-δ (sym (++-assoc Δ₁ [ y ] Δ₂)) d

    eq2 : δ step1' ≡ δ step1
    eq2 = subst-preserves-δ
      (++-assoc Δ₁ [ y ] (x ∷ remove-first x Δ₂ p))
      step1
  in eq2 ∙ ih ∙ eq1

bring-to-front-r-preserves-δ : ∀ {Γ} (Δ : Ctx) (x : PFormula)
  (p : x ∈ Δ) (d : Γ ⊢ Δ)
  → δ (bring-to-front-r Δ x p d) ≡ δ d
bring-to-front-r-preserves-δ Δ x p d =
  bring-to-front-ctx-r-preserves-δ [] Δ x p d

put-back-ctx-preserves-δ : ∀ {Δ} (Γ₁ Γ₂ : Ctx) (x : PFormula)
  (p : x ∈ Γ₂) (d : (Γ₁ ++ x ∷ remove-first x Γ₂ p) ⊢ Δ)
  → δ (put-back-ctx Γ₁ Γ₂ x p d) ≡ δ d
put-back-ctx-preserves-δ Γ₁ ._ x (here {xs = xs} eq) d =
  subst-preserves-δ-ctx (cong (λ z → Γ₁ ++ z ∷ xs) eq) d
put-back-ctx-preserves-δ {Δ} Γ₁ ._ x
  (there {x = y} {xs = Γ₂} p) d =
  let
    step1 = ExchangeL {Γ₁ = Γ₁} {Γ₂ = remove-first x Γ₂ p} d
    step1' = subst (_⊢ Δ)
      (sym (++-assoc Γ₁ [ y ] (x ∷ remove-first x Γ₂ p)))
      step1
    res = put-back-ctx (Γ₁ ++ [ y ]) Γ₂ x p step1'

    ih : δ res ≡ δ step1'
    ih = put-back-ctx-preserves-δ (Γ₁ ++ [ y ]) Γ₂ x p step1'

    eq1 : δ step1' ≡ δ step1
    eq1 = subst-preserves-δ-ctx
      (sym (++-assoc Γ₁ [ y ] (x ∷ remove-first x Γ₂ p)))
      step1

    eq2 : δ (subst (_⊢ Δ) (++-assoc Γ₁ [ y ] Γ₂) res) ≡ δ res
    eq2 = subst-preserves-δ-ctx (++-assoc Γ₁ [ y ] Γ₂) res
  in eq2 ∙ ih ∙ eq1

put-back-preserves-δ : ∀ {Δ} (Γ : Ctx) (x : PFormula)
  (p : x ∈ Γ) (d : x ∷ remove-first x Γ p ⊢ Δ)
  → δ (put-back Γ x p d) ≡ δ d
put-back-preserves-δ Γ x p d =
  put-back-ctx-preserves-δ [] Γ x p d

put-back-ctx-r-preserves-δ : ∀ {Γ} (Δ₁ Δ₂ : Ctx) (x : PFormula)
  (p : x ∈ Δ₂) (d : Γ ⊢ (Δ₁ ++ x ∷ remove-first x Δ₂ p))
  → δ (put-back-ctx-r Δ₁ Δ₂ x p d) ≡ δ d
put-back-ctx-r-preserves-δ Δ₁ ._ x (here {xs = xs} eq) d =
  subst-preserves-δ (cong (λ z → Δ₁ ++ z ∷ xs) eq) d
put-back-ctx-r-preserves-δ {Γ} Δ₁ ._ x
  (there {x = y} {xs = Δ₂} p) d =
  let
    step1 = ExchangeR {Δ₁ = Δ₁} {Δ₂ = remove-first x Δ₂ p} d
    step1' = subst (Γ ⊢_)
      (sym (++-assoc Δ₁ [ y ] (x ∷ remove-first x Δ₂ p)))
      step1
    res = put-back-ctx-r (Δ₁ ++ [ y ]) Δ₂ x p step1'

    ih : δ res ≡ δ step1'
    ih = put-back-ctx-r-preserves-δ (Δ₁ ++ [ y ]) Δ₂ x p step1'

    eq1 : δ step1' ≡ δ step1
    eq1 = subst-preserves-δ
      (sym (++-assoc Δ₁ [ y ] (x ∷ remove-first x Δ₂ p)))
      step1

    eq2 : δ (subst (Γ ⊢_) (++-assoc Δ₁ [ y ] Δ₂) res) ≡ δ res
    eq2 = subst-preserves-δ (++-assoc Δ₁ [ y ] Δ₂) res
  in eq2 ∙ ih ∙ eq1

put-back-r-preserves-δ : ∀ {Γ} (Δ : Ctx) (x : PFormula)
  (p : x ∈ Δ) (d : Γ ⊢ x ∷ remove-first x Δ p)
  → δ (put-back-r Δ x p d) ≡ δ d
put-back-r-preserves-δ Δ x p d =
  put-back-ctx-r-preserves-δ [] Δ x p d

weakening-left-preserves-δ : ∀ {Γ Δ} (Σ : Ctx) (d : Γ ⊢ Δ)
  → δ (weakening-left Σ d) ≡ δ d
weakening-left-preserves-δ [] d = refl
weakening-left-preserves-δ (x ∷ Σ) d =
  weakening-left-preserves-δ Σ d

weakening-right-preserves-δ : ∀ {Γ Δ} (Σ : Ctx) (d : Γ ⊢ Δ)
  → δ (weakening-right Σ d) ≡ δ d
weakening-right-preserves-δ [] d = refl
weakening-right-preserves-δ (x ∷ Σ) d =
  weakening-right-preserves-δ Σ d

subset-weakening-left-gen-preserves-δ : ∀ {Γ Γ' Σ Δ}
  (sub : Γ ⊆ Γ') (d : (Γ ++ Σ) ⊢ Δ)
  → δ (subset-weakening-left-gen sub d) ≡ δ d
subset-weakening-left-gen-preserves-δ {[]} {Γ'} {Σ} sub d =
  weakening-left-preserves-δ Γ' d
subset-weakening-left-gen-preserves-δ {x ∷ Γ} {Γ'} {Σ} {Δ}
  sub d with x ∈? Γ
... | yes xInΓ =
  let
    d' : x ∷ x ∷ remove-first x (Γ ++ Σ) (∈-++⁺ˡ xInΓ) ⊢ Δ
    d' = bring-to-front-ctx [ x ] (Γ ++ Σ) x (∈-++⁺ˡ xInΓ) d

    d'' : x ∷ remove-first x (Γ ++ Σ) (∈-++⁺ˡ xInΓ) ⊢ Δ
    d'' = ContractL d'

    d-back = put-back (Γ ++ Σ) x (∈-++⁺ˡ xInΓ) d''

    sub' : Γ ⊆ Γ'
    sub' yIn = sub (there yIn)

    ih : δ (subset-weakening-left-gen sub' d-back) ≡ δ d-back
    ih = subset-weakening-left-gen-preserves-δ sub' d-back

    eq1 : δ d' ≡ δ d
    eq1 = bring-to-front-ctx-preserves-δ [ x ] (Γ ++ Σ) x (∈-++⁺ˡ xInΓ) d

    eq2 : δ d-back ≡ δ d''
    eq2 = put-back-preserves-δ (Γ ++ Σ) x (∈-++⁺ˡ xInΓ) d''
  in ih ∙ eq2 ∙ eq1

... | no xNotInΓ =
  let
    xInΓ' : x ∈ Γ'
    xInΓ' = sub ∈-here

    gammaSub : Γ ⊆ remove-first x Γ' xInΓ'
    gammaSub {y} yIn =
      let
        yInΓ' = sub (there yIn)
        neq : Neg (x ≡ y)
        neq p = xNotInΓ (subst (_∈ Γ) (sym p) yIn)
      in mem-remove-first x Γ' xInΓ' y yInΓ' neq

    d-perm : (Γ ++ x ∷ Σ) ⊢ Δ
    d-perm = put-back (Γ ++ x ∷ Σ) x (∈-++⁺ʳ Γ ∈-here)
      (subst (λ G → x ∷ G ⊢ Δ)
        (sym (remove-first-++-r x Γ (x ∷ Σ) ∈-here)) d)

    ih : δ (subset-weakening-left-gen gammaSub d-perm) ≡ δ d-perm
    ih = subset-weakening-left-gen-preserves-δ gammaSub d-perm

    d-front = bring-to-front
      ((remove-first x Γ' xInΓ') ++ x ∷ Σ) x
      (∈-++⁺ʳ _ ∈-here)
      (subset-weakening-left-gen gammaSub d-perm)

    d-front' : x ∷ (remove-first x Γ' xInΓ') ++ Σ ⊢ Δ
    d-front' = subst (λ G → x ∷ G ⊢ Δ)
      (remove-first-++-r x
        (remove-first x Γ' xInΓ') (x ∷ Σ) ∈-here)
      d-front

    res : (Γ' ++ Σ) ⊢ Δ
    res = put-back (Γ' ++ Σ) x (∈-++⁺ˡ xInΓ')
      (subst (λ G → x ∷ G ⊢ Δ)
        (sym (remove-first-++-l x Γ' Σ xInΓ'))
        d-front')

    eqd-perm : δ d-perm ≡ δ d
    eqd-perm =
      put-back-preserves-δ (Γ ++ x ∷ Σ) x (∈-++⁺ʳ Γ ∈-here)
        (subst (λ G → x ∷ G ⊢ Δ)
          (sym (remove-first-++-r x Γ (x ∷ Σ) ∈-here)) d)
      ∙ subst-preserves-δ-ctx
          (cong (x ∷_)
            (sym (remove-first-++-r x Γ (x ∷ Σ) ∈-here))) d

    eqfront : δ d-front' ≡ δ (subset-weakening-left-gen gammaSub d-perm)
    eqfront =
      subst-preserves-δ-ctx
        (cong (x ∷_)
          (remove-first-++-r x (remove-first x Γ' xInΓ')
             (x ∷ Σ) ∈-here)) d-front
      ∙ bring-to-front-preserves-δ
          ((remove-first x Γ' xInΓ') ++ x ∷ Σ) x
          (∈-++⁺ʳ _ ∈-here)
          (subset-weakening-left-gen gammaSub d-perm)

    eqres : δ res ≡ δ d-front'
    eqres =
      put-back-preserves-δ (Γ' ++ Σ) x (∈-++⁺ˡ xInΓ')
        (subst (λ G → x ∷ G ⊢ Δ)
          (sym (remove-first-++-l x Γ' Σ xInΓ')) d-front')
      ∙ subst-preserves-δ-ctx
          (cong (x ∷_) (sym (remove-first-++-l x Γ' Σ xInΓ')))
          d-front'
  in eqres ∙ eqfront ∙ ih ∙ eqd-perm

subset-weakening-right-gen-preserves-δ : ∀ {Δ Δ' Σ Γ}
  (sub : Δ ⊆ Δ') (d : Γ ⊢ (Δ ++ Σ))
  → δ (subset-weakening-right-gen sub d) ≡ δ d
subset-weakening-right-gen-preserves-δ {[]} {Δ'} {Σ} sub d =
  weakening-right-preserves-δ Δ' d
subset-weakening-right-gen-preserves-δ {x ∷ Δ} {Δ'} {Σ} {Γ}
  sub d with x ∈? Δ
... | yes xInΔ =
  let
    d' = bring-to-front-ctx-r [ x ] (Δ ++ Σ) x (∈-++⁺ˡ xInΔ) d
    d'' = ContractR d'
    d-back = put-back-r (Δ ++ Σ) x (∈-++⁺ˡ xInΔ) d''

    sub' : Δ ⊆ Δ'
    sub' yIn = sub (there yIn)

    ih : δ (subset-weakening-right-gen sub' d-back) ≡ δ d-back
    ih = subset-weakening-right-gen-preserves-δ sub' d-back

    eq1 : δ d' ≡ δ d
    eq1 = bring-to-front-ctx-r-preserves-δ [ x ] (Δ ++ Σ) x (∈-++⁺ˡ xInΔ) d

    eq2 : δ d-back ≡ δ d''
    eq2 = put-back-r-preserves-δ (Δ ++ Σ) x (∈-++⁺ˡ xInΔ) d''
  in ih ∙ eq2 ∙ eq1

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

    ih : δ (subset-weakening-right-gen deltaSub d-perm) ≡ δ d-perm
    ih = subset-weakening-right-gen-preserves-δ deltaSub d-perm

    d-front = bring-to-front-r
      ((remove-first x Δ' xInΔ') ++ x ∷ Σ) x
      (∈-++⁺ʳ _ ∈-here)
      (subset-weakening-right-gen deltaSub d-perm)

    d-front' : Γ ⊢ x ∷ (remove-first x Δ' xInΔ') ++ Σ
    d-front' = subst (λ D → Γ ⊢ x ∷ D)
      (remove-first-++-r x
        (remove-first x Δ' xInΔ') (x ∷ Σ) ∈-here)
      d-front

    res = put-back-r (Δ' ++ Σ) x (∈-++⁺ˡ xInΔ')
      (subst (λ D → Γ ⊢ x ∷ D)
        (sym (remove-first-++-l x Δ' Σ xInΔ'))
        d-front')

    eqd-perm : δ d-perm ≡ δ d
    eqd-perm =
      put-back-r-preserves-δ (Δ ++ x ∷ Σ) x (∈-++⁺ʳ Δ ∈-here)
        (subst (λ D → Γ ⊢ x ∷ D)
          (sym (remove-first-++-r x Δ (x ∷ Σ) ∈-here)) d)
      ∙ subst-preserves-δ
          (cong (x ∷_)
            (sym (remove-first-++-r x Δ (x ∷ Σ) ∈-here))) d

    eqfront : δ d-front' ≡ δ (subset-weakening-right-gen deltaSub d-perm)
    eqfront =
      subst-preserves-δ
        (cong (x ∷_)
          (remove-first-++-r x
             (remove-first x Δ' xInΔ') (x ∷ Σ) ∈-here))
        d-front
      ∙ bring-to-front-r-preserves-δ
          ((remove-first x Δ' xInΔ') ++ x ∷ Σ) x
          (∈-++⁺ʳ _ ∈-here)
          (subset-weakening-right-gen deltaSub d-perm)

    eqres : δ res ≡ δ d-front'
    eqres =
      put-back-r-preserves-δ (Δ' ++ Σ) x (∈-++⁺ˡ xInΔ')
        (subst (λ D → Γ ⊢ x ∷ D)
          (sym (remove-first-++-l x Δ' Σ xInΔ')) d-front')
      ∙ subst-preserves-δ
          (cong (x ∷_) (sym (remove-first-++-l x Δ' Σ xInΔ')))
          d-front'
  in eqres ∙ eqfront ∙ ih ∙ eqd-perm

structural-preserves-δ : ∀ {Γ Δ Γ' Δ'}
  (subG : Γ ⊆ Γ') (subD : Δ ⊆ Δ') (p : Γ ⊢ Δ)
  → δ (structural subG subD p) ≡ δ p
structural-preserves-δ {Γ} {Δ} {Γ'} {Δ'} subG subD d =
  let
    step1 = subset-weakening-left-gen {Σ = []} subG
      (subst (_⊢ Δ) (sym (++-unit-r Γ)) d)
    step1' = subst (_⊢ Δ) (++-unit-r Γ') step1

    step2 = subset-weakening-right-gen {Σ = []} subD
      (subst (Γ' ⊢_) (sym (++-unit-r Δ)) step1')
    step2' = subst (Γ' ⊢_) (++-unit-r Δ') step2

    eq1 = subst-preserves-δ-ctx (sym (++-unit-r Γ)) d
    eq2 = subset-weakening-left-gen-preserves-δ subG
      (subst (_⊢ Δ) (sym (++-unit-r Γ)) d)
    eq3 = subst-preserves-δ-ctx (++-unit-r Γ') step1
    eq4 = subst-preserves-δ (sym (++-unit-r Δ)) step1'
    eq5 = subset-weakening-right-gen-preserves-δ subD
      (subst (Γ' ⊢_) (sym (++-unit-r Δ)) step1')
    eq6 = subst-preserves-δ (++-unit-r Δ') step2
  in eq6 ∙ eq5 ∙ eq4 ∙ eq3 ∙ eq2 ∙ eq1

------------------------------------------------------------------------
-- -pf normalization and membership lemmas

pf-cons-eq : ∀ {φ ψ : PFormula} {Γ : Ctx}
  → ψ ≡ φ → ((ψ ∷ Γ) -pf φ) ≡ (Γ -pf φ)
pf-cons-eq {φ} {ψ} {Γ} eq with ψ ≟pf φ
... | yes _ = refl
... | no ¬p with ¬p eq
... | ()

pf-cons-neq : ∀ {φ ψ : PFormula} {Γ : Ctx}
  → Neg (φ ≡ ψ) → ((ψ ∷ Γ) -pf φ) ≡ (ψ ∷ (Γ -pf φ))
pf-cons-neq {φ} {ψ} {Γ} neq with ψ ≟pf φ
... | yes p = ⊥-elim (neq (sym p))
... | no _ = refl

pf-++ : ∀ (φ : PFormula) (Γ Δ : Ctx)
  → ((Γ ++ Δ) -pf φ) ≡ ((Γ -pf φ) ++ (Δ -pf φ))
pf-++ φ [] Δ = refl
pf-++ φ (x ∷ Γ) Δ with x ≟pf φ
... | yes _ = pf-++ φ Γ Δ
... | no _ = cong (x ∷_) (pf-++ φ Γ Δ)

pf-remove-mem : ∀ {x y : PFormula} {Γ : Ctx}
  → y ∈ (Γ -pf x) → (y ∈ Γ) × Neg (x ≡ y)
pf-remove-mem {x} {y} {[]} ()
pf-remove-mem {x} {y} {z ∷ Γ} yIn with z ≟pf x
... | yes z≡x =
  let
    rec = pf-remove-mem {x} {y} {Γ} yIn
  in there (fst rec) , snd rec
... | no z≢x with yIn
... | here y≡z = here y≡z , (λ x≡y → z≢x (sym (x≡y ∙ y≡z)))
... | there yIn' =
  let
    rec = pf-remove-mem {x} {y} {Γ} yIn'
  in there (fst rec) , snd rec

pf-⊆ : ∀ {φ : PFormula} {Γ : Ctx} → (Γ -pf φ) ⊆ Γ
pf-⊆ yIn = fst (pf-remove-mem yIn)

pf-singleton-eq : ∀ {φ ψ : PFormula}
  → φ ≡ ψ → ([ ψ ] -pf φ) ≡ []
pf-singleton-eq {φ} {ψ} eq = pf-cons-eq {Γ = []} (sym eq)

pf-singleton-neq : ∀ {φ ψ : PFormula}
  → Neg (φ ≡ ψ) → ([ ψ ] -pf φ) ≡ [ ψ ]
pf-singleton-neq {φ} {ψ} neq = pf-cons-neq {Γ = []} neq

------------------------------------------------------------------------
-- Subset helpers for cut reconstruction

subset-remove-left : (Γ₁ Γ₂ : Ctx) (A : PFormula)
  → (Γ₁ ++ (Γ₂ -pf A)) ⊆ (Γ₁ ++ Γ₂)
subset-remove-left Γ₁ Γ₂ A {y} yIn with ∈-++⁻ Γ₁ yIn
... | inl yInΓ₁ = ∈-++⁺ˡ yInΓ₁
... | inr yInΓ₂-A = ∈-++⁺ʳ Γ₁ (pf-⊆ {φ = A} {Γ = Γ₂} yInΓ₂-A)

subset-remove-right : (Δ₁ Δ₂ : Ctx) (A : PFormula)
  → ((Δ₁ -pf A) ++ Δ₂) ⊆ (Δ₁ ++ Δ₂)
subset-remove-right Δ₁ Δ₂ A {y} yIn with ∈-++⁻ (Δ₁ -pf A) yIn
... | inl yInΔ₁-A = ∈-++⁺ˡ (pf-⊆ {φ = A} {Γ = Δ₁} yInΔ₁-A)
... | inr yInΔ₂ = ∈-++⁺ʳ Δ₁ yInΔ₂

cut-sub-left : (Γ₁ Γ₂ : Ctx) (A : Formula) (α : Position)
  → (Γ₁ ++ ((Γ₂ ++ [ (A ^ α) ]) -pf (A ^ α))) ⊆ (Γ₁ ++ Γ₂)
cut-sub-left Γ₁ Γ₂ A α {y} yIn with ∈-++⁻ Γ₁ yIn
... | inl yInΓ₁ = ∈-++⁺ˡ yInΓ₁
... | inr yInRem with pf-remove-mem {x = A ^ α} {y = y} {Γ = Γ₂ ++ [ A ^ α ]} yInRem
... | yInΓ₂A , notEq with ∈-++⁻ Γ₂ yInΓ₂A
... | inl yInΓ₂ = ∈-++⁺ʳ Γ₁ yInΓ₂
... | inr yInSingleton with yInSingleton
... | here p = ⊥-elim (notEq (sym p))
... | there ()

cut-sub-right : (Δ₁ Δ₂ : Ctx) (A : Formula) (α : Position)
  → ((((A ^ α) ∷ Δ₁) -pf (A ^ α)) ++ Δ₂) ⊆ (Δ₁ ++ Δ₂)
cut-sub-right Δ₁ Δ₂ A α {y} yIn with ∈-++⁻ (((A ^ α) ∷ Δ₁) -pf (A ^ α)) yIn
... | inr yInΔ₂ = ∈-++⁺ʳ Δ₁ yInΔ₂
... | inl yInRem with pf-remove-mem {x = A ^ α} {y = y} {Γ = (A ^ α) ∷ Δ₁} yInRem
... | yInAΔ₁ , notEq with ∈-++⁻ [ A ^ α ] yInAΔ₁
... | inr yInΔ₁ = ∈-++⁺ˡ yInΔ₁
... | inl yInSingleton with yInSingleton
... | here p = ⊥-elim (notEq (sym p))
... | there ()

------------------------------------------------------------------------
-- Formula/PFormula injectors

Not-inj : ∀ {A B : Formula} → Not A ≡ Not B → A ≡ B
Not-inj eq = cong (λ { (Not x) → x ; x → x }) eq

And-inj-l : ∀ {A B C D : Formula} → And A B ≡ And C D → A ≡ C
And-inj-l eq = cong (λ { (And x _) → x ; x → x }) eq

And-inj-r : ∀ {A B C D : Formula} → And A B ≡ And C D → B ≡ D
And-inj-r eq = cong (λ { (And _ x) → x ; x → x }) eq

Or-inj-l : ∀ {A B C D : Formula} → Or A B ≡ Or C D → A ≡ C
Or-inj-l eq = cong (λ { (Or x _) → x ; x → x }) eq

Or-inj-r : ∀ {A B C D : Formula} → Or A B ≡ Or C D → B ≡ D
Or-inj-r eq = cong (λ { (Or _ x) → x ; x → x }) eq

Imp-inj-l : ∀ {A B C D : Formula} → (A ⇒ B) ≡ (C ⇒ D) → A ≡ C
Imp-inj-l eq = cong (λ { (x ⇒ _) → x ; x → x }) eq

Imp-inj-r : ∀ {A B C D : Formula} → (A ⇒ B) ≡ (C ⇒ D) → B ≡ D
Imp-inj-r eq = cong (λ { (_ ⇒ x) → x ; x → x }) eq

□-inj : ∀ {A B : Formula} → □ A ≡ □ B → A ≡ B
□-inj eq = cong (λ { (□ x) → x ; x → x }) eq

♢-inj : ∀ {A B : Formula} → ♢ A ≡ ♢ B → A ≡ B
♢-inj eq = cong (λ { (♢ x) → x ; x → x }) eq

pf-form : ∀ {A B : Formula} {s t : Position} → (A ^ s) ≡ (B ^ t) → A ≡ B
pf-form = cong PFormula.form

pf-pos : ∀ {A B : Formula} {s t : Position} → (A ^ s) ≡ (B ^ t) → s ≡ t
pf-pos = cong PFormula.pos
