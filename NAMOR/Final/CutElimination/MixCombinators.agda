{-# OPTIONS --safe #-}

open import NAMOR.Final.Syntax using (Logic)

module NAMOR.Final.CutElimination.MixCombinators (M : Logic) where

open import Cubical.Foundations.Prelude
  using (Type; _≡_; refl; sym; subst; cong; _∙_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; max)
open import Cubical.Data.Nat.Properties using (+-zero; +-suc)
open import Cubical.Data.Nat.Order
  using (_≤_; _<_; ≤-refl; ≤-trans; suc-≤-suc; <-weaken; ¬-<-zero; pred-≤-pred;
         <-+k; <-k+; left-≤-max; right-≤-max)
open import Cubical.Data.Sigma using (Σ; _×_; _,_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥
open import Cubical.Induction.WellFounded using (Acc; acc)

open import NAMOR.List.Membership using (_⊆_)
open import NAMOR.Final.Syntax hiding (Logic)
open import NAMOR.Final.System M
open import NAMOR.Final.Structural M using (structural)
open import NAMOR.Final.CutElimination.Defs M using (δ)
open import NAMOR.Final.CutElimination.Base M
  using (structural-preserves-δ; subst-preserves-δ; subst-preserves-δ-ctx)

+-suc-1 : ∀ n → n + 1 ≡ suc n
+-suc-1 n = +-suc n 0 ∙ cong suc (+-zero n)

structural-δ : ∀ {Γ Δ Γ' Δ' n}
  → Γ ⊆ Γ' → Δ ⊆ Δ' → (Π : Γ ⊢ Δ) → δ Π ≤ n
  → Σ (Γ' ⊢ Δ') (λ Π' → δ Π' ≤ n)
structural-δ {n = n} subL subR Π dΠ≤n =
  let Π' = structural subL subR Π in
  Π' , subst (λ z → z ≤ n) (sym (structural-preserves-δ subL subR Π)) dΠ≤n

subst-δ-Δ : ∀ {Γ Δ Δ' n}
  → (eq : Δ ≡ Δ') → (Π : Γ ⊢ Δ) → δ Π ≤ n
  → Σ (Γ ⊢ Δ') (λ Π' → δ Π' ≤ n)
subst-δ-Δ {Γ = Γ} {n = n} eq Π dΠ≤n =
  let Π' = subst (Γ ⊢_) eq Π in
  Π' , subst (λ z → z ≤ n) (sym (subst-preserves-δ eq Π)) dΠ≤n

subst-δ-Γ : ∀ {Γ Γ' Δ n}
  → (eq : Γ ≡ Γ') → (Π : Γ ⊢ Δ) → δ Π ≤ n
  → Σ (Γ' ⊢ Δ) (λ Π' → δ Π' ≤ n)
subst-δ-Γ {Δ = Δ} {n = n} eq Π dΠ≤n =
  let Π' = subst (_⊢ Δ) eq Π in
  Π' , subst (λ z → z ≤ n) (sym (subst-preserves-δ-ctx eq Π)) dΠ≤n

step-left-+1 : ∀ (a b : ℕ) → a + b < (a + 1) + b
step-left-+1 a b =
  subst (a + b <_) (sym (cong (_+ b) (+-suc-1 a)))
    (<-+k {k = b} (suc-≤-suc ≤-refl))

step-right-+1 : ∀ (a b : ℕ) → a + b < a + (b + 1)
step-right-+1 a b =
  subst (a + b <_) (sym (cong (a +_) (+-suc-1 b)))
    (<-k+ {k = a} (suc-≤-suc ≤-refl))

step-left-binary₁ : ∀ (a b c : ℕ) → a + c < (max a b + 1) + c
step-left-binary₁ a b c =
  subst (a + c <_) (sym (cong (_+ c) (+-suc-1 (max a b))))
    (<-+k {k = c} (suc-≤-suc left-≤-max))

step-left-binary₂ : ∀ (a b c : ℕ) → b + c < (max a b + 1) + c
step-left-binary₂ a b c =
  subst (b + c <_) (sym (cong (_+ c) (+-suc-1 (max a b))))
    (<-+k {k = c} (suc-≤-suc (right-≤-max {n = b} {m = a})))

step-right-binary₁ : ∀ (a b c : ℕ) → c + a < c + (max a b + 1)
step-right-binary₁ a b c =
  subst (c + a <_) (sym (cong (c +_) (+-suc-1 (max a b))))
    (<-k+ {k = c} (suc-≤-suc left-≤-max))

step-right-binary₂ : ∀ (a b c : ℕ) → c + b < c + (max a b + 1)
step-right-binary₂ a b c =
  subst (c + b <_) (sym (cong (c +_) (+-suc-1 (max a b))))
    (<-k+ {k = c} (suc-≤-suc (right-≤-max {n = b} {m = a})))

------------------------------------------------------------------------
-- Well-foundedness of < on ℕ

private
  acc≤ : (n : ℕ) → (m : ℕ) → m ≤ n → Acc _<_ m
  acc≤ n zero _ = acc λ k k<0 → ⊥.rec (¬-<-zero k<0)
  acc≤ zero (suc m) sm≤0 = ⊥.rec (¬-<-zero sm≤0)
  acc≤ (suc n) (suc m) sm≤sn =
    acc λ k k<sm →
      acc≤ n k (≤-trans (pred-≤-pred k<sm) (pred-≤-pred sm≤sn))

<-wf : (n : ℕ) → Acc _<_ n
<-wf n = acc λ m m<n → acc≤ n m (<-weaken m<n)

------------------------------------------------------------------------
-- Lexicographic ordering on ℕ × ℕ
--
-- Primary: degree of cut formula (decreases in principal cases)
-- Secondary: mixHeight (decreases in non-principal cases)

_<Lex_ : (ℕ × ℕ) → (ℕ × ℕ) → Type
(d₁ , h₁) <Lex (d₂ , h₂) = (d₁ < d₂) ⊎ ((d₁ ≡ d₂) × (h₁ < h₂))

private
  <Lex-acc-inner : ∀ d → (∀ d' → d' < d → ∀ h' → Acc _<Lex_ (d' , h'))
                 → ∀ h → Acc _<_ h → Acc _<Lex_ (d , h)
  <Lex-acc-inner d recD h (acc recH) = acc helper
    where
      helper : ∀ p → p <Lex (d , h) → Acc _<Lex_ p
      helper (d' , h') (inl d'<d) = recD d' d'<d h'
      helper (d' , h') (inr (d'≡d , h'<h)) =
        subst (λ x → Acc _<Lex_ (x , h')) (sym d'≡d)
              (<Lex-acc-inner d recD h' (recH h' h'<h))

  <Lex-acc-outer : ∀ d → Acc _<_ d → ∀ h → Acc _<Lex_ (d , h)
  <Lex-acc-outer d (acc recD) h =
    <Lex-acc-inner d
      (λ d' d'<d h' → <Lex-acc-outer d' (recD d' d'<d) h')
      h (<-wf h)

<Lex-wf : ∀ p → Acc _<Lex_ p
<Lex-wf (d , h) = <Lex-acc-outer d (<-wf d) h

<Lex-inv : ∀ {p q} → Acc _<Lex_ p → q <Lex p → Acc _<Lex_ q
<Lex-inv (acc f) lt = f _ lt

-- Convenience: same degree, smaller height → <Lex
step-lex-height : ∀ {n h h'} → h' < h → (n , h') <Lex (n , h)
step-lex-height h'<h = inr (refl , h'<h)

-- Convenience: smaller degree → <Lex (any height)
step-lex-degree : ∀ {d d' h h'} → d' < d → (d' , h') <Lex (d , h)
step-lex-degree d'<d = inl d'<d
