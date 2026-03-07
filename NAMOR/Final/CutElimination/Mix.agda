{-# OPTIONS #-}

open import NAMOR.Final.Syntax using (Logic)

module NAMOR.Final.CutElimination.Mix (M : Logic) where

open import Cubical.Foundations.Prelude
  using (Type; _≡_; refl; sym; subst; cong; cong₂; _∙_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; max)
open import Cubical.Data.Nat.Properties using (maxComm)
open import Cubical.Data.Nat.Order
  using (_≤_; _<_; ≤-refl; suc-≤-suc; ≤-trans; zero-≤; ¬-<-zero; <-weaken; pred-≤-pred;
         left-≤-max; right-≤-max)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd; _×_)
open import Cubical.Data.List using (_∷_; _++_; []; [_])
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary
  using (Dec; yes; no)
  renaming (¬_ to Neg)
open import Cubical.Induction.WellFounded using (Acc; acc)

open import NAMOR.List.Any using (here; there)
open import NAMOR.List.Prefix using (_⊑_; ⊑-++; ⊑-trans)
open import NAMOR.List.Membership
  using (_∈_; _⊆_; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-here)
open import NAMOR.Final.Syntax hiding (Logic)
open import NAMOR.Final.System M
open import NAMOR.Final.Structural M using (structural)
open import NAMOR.Final.InitLemmas
  using (∈Init-∷; ∈Init-++⁺ˡ; ∈Init-++⁺ʳ; ∈Init-++⁻;
         ∉Init-∷; ∉Init-++; modalConstraint-weaken-left; modalConstraint-weaken-right)
open import NAMOR.Final.CutElimination.Defs M
  using (degree; height; δ; max-least)
open import NAMOR.Final.CutElimination.Base M
  using (pf-cons-eq; pf-cons-neq; pf-singleton-neq; pf-remove-mem; pf-++;
         Not-inj; And-inj-l; And-inj-r; Imp-inj-l; Imp-inj-r; pf-form; pf-pos; pf-⊆)
open import NAMOR.Final.CutElimination.MixCombinators M
  using (structural-δ; subst-δ-Δ; subst-δ-Γ;
         _<Lex_; <Lex-wf; <Lex-inv; step-lex-height; step-lex-degree; <-wf;
         step-left-+1; step-right-+1;
         step-left-binary₁; step-left-binary₂; step-right-binary₁; step-right-binary₂)
open import NAMOR.Final.CutElimination.Macros using (solveCtx⊆!)
open import NAMOR.Final.CutElimination.ProofSubst M
  using (SubstSideCond; substProofRaw)

private postulate TODO : ∀ {ℓ} {A : Type ℓ} → A

------------------------------------------------------------------------
-- Public Mix API consumed by CutElimination.

-- %<*mixAPI>
MixAPI : Type
MixAPI =
  ∀ {Γ Δ Γ' Δ'} {A : Formula} {α : Position}
  → (n : ℕ) → degree A ≡ n
  → (Π : Γ ⊢ Δ)
  → (Π' : Γ' ⊢ Δ')
  → δ Π ≤ n → δ Π' ≤ n
  → cutConstraint M A α Γ Γ' Δ Δ'
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
-- %</mixAPI>

-- %<*mixHeight>
mixHeight : ∀ {Γ Δ Γ' Δ'} → Γ ⊢ Δ → Γ' ⊢ Δ' → ℕ
mixHeight Π Π' = height Π + height Π'
-- %</mixHeight>

------------------------------------------------------------------------
-- Strict subformula degree facts used by principal recursion.

degree-sub-Not : ∀ {A : Formula} → degree A < degree (Not A)
degree-sub-Not = suc-≤-suc ≤-refl

degree-sub-AndL : ∀ {A B : Formula} → degree A < degree (And A B)
degree-sub-AndL = suc-≤-suc left-≤-max

degree-sub-AndR : ∀ {A B : Formula} → degree B < degree (And A B)
degree-sub-AndR {A = A} {B = B} = suc-≤-suc (right-≤-max {n = degree B} {m = degree A})

degree-sub-OrL : ∀ {A B : Formula} → degree A < degree (Or A B)
degree-sub-OrL = suc-≤-suc left-≤-max

degree-sub-OrR : ∀ {A B : Formula} → degree B < degree (Or A B)
degree-sub-OrR {A = A} {B = B} = suc-≤-suc (right-≤-max {n = degree B} {m = degree A})

degree-sub-ImpL : ∀ {A B : Formula} → degree A < degree (A ⇒ B)
degree-sub-ImpL = suc-≤-suc left-≤-max

degree-sub-ImpR : ∀ {A B : Formula} → degree B < degree (A ⇒ B)
degree-sub-ImpR {A = A} {B = B} = suc-≤-suc (right-≤-max {n = degree B} {m = degree A})

degree-sub-Box : ∀ {A : Formula} → degree A < degree (□ A)
degree-sub-Box = suc-≤-suc ≤-refl

degree-sub-Dia : ∀ {A : Formula} → degree A < degree (♢ A)
degree-sub-Dia = suc-≤-suc ≤-refl

lift-≤-from-< :
  ∀ {d m n : ℕ}
  → d ≤ m → m < n → d ≤ n
lift-≤-from-< d≤m m<n = ≤-trans d≤m (<-weaken m<n)

private
  acc≤ : (n : ℕ) → (m : ℕ) → m ≤ n → Acc _<_ m
  acc≤ n zero _ = acc λ k k<0 → ⊥.rec (¬-<-zero k<0)
  acc≤ zero (suc m) sm≤0 = ⊥.rec (¬-<-zero sm≤0)
  acc≤ (suc n) (suc m) sm≤sn =
    acc λ k k<sm →
      acc≤ n k (≤-trans (pred-≤-pred k<sm) (pred-≤-pred sm≤sn))

subset-refl : ∀ {Γ : Ctx} → Γ ⊆ Γ
subset-refl = solveCtx⊆!

subset-cons-append-mid :
  ∀ (Σ Δ : Ctx) (x : PFormula)
  → (x ∷ (Σ ++ Δ)) ⊆ (Σ ++ (x ∷ Δ))
subset-cons-append-mid Σ Δ x = solveCtx⊆!

subset-append-mid-cons :
  ∀ (Σ Δ : Ctx) (x : PFormula)
  → (Σ ++ (x ∷ Δ)) ⊆ (x ∷ (Σ ++ Δ))
subset-append-mid-cons Σ Δ x = solveCtx⊆!

subset-drop-dup-head :
  ∀ (x : PFormula) (Γ : Ctx)
  → (x ∷ x ∷ Γ) ⊆ (x ∷ Γ)
subset-drop-dup-head x Γ = solveCtx⊆!

subset-drop-dup-mid :
  ∀ (Σ Δ : Ctx) (x : PFormula)
  → (Σ ++ (x ∷ x ∷ Δ)) ⊆ (Σ ++ (x ∷ Δ))
subset-drop-dup-mid Σ Δ x = solveCtx⊆!

subset-append-right-cons :
  ∀ (Σ Δ : Ctx) (x : PFormula)
  → (Σ ++ Δ) ⊆ (Σ ++ (x ∷ Δ))
subset-append-right-cons Σ Δ x = solveCtx⊆!

subset-swap-mid :
  ∀ (Σ Δ : Ctx) (c d : PFormula)
  → (Σ ++ (c ∷ d ∷ Δ)) ⊆ (Σ ++ (d ∷ c ∷ Δ))
subset-swap-mid Σ Δ c d = solveCtx⊆!

subset-move-mid-to-end :
  ∀ (Σ Δ : Ctx) (x : PFormula)
  → (Σ ++ (x ∷ Δ)) ⊆ ((Σ ++ Δ) ++ [ x ])
subset-move-mid-to-end Σ Δ x = solveCtx⊆!

subset-move-end-to-mid :
  ∀ (Σ Δ : Ctx) (x : PFormula)
  → ((Σ ++ Δ) ++ [ x ]) ⊆ (Σ ++ (x ∷ Δ))
subset-move-end-to-mid Σ Δ x = solveCtx⊆!

------------------------------------------------------------------------
-- Generic `-pf` membership introduction:
-- if y is in Γ and y ≠ x, then y is in Γ -pf x.

pf-keep : ∀ {x y : PFormula} {Γ : Ctx}
  → y ∈ Γ → Neg (y ≡ x) → y ∈ (Γ -pf x)
pf-keep {x} {y} {[]} () neq
pf-keep {x} {y} {Γ = z ∷ Γ} (here y≡z) neq with z ≟pf x
... | yes z≡x = ⊥.elim (neq (y≡z ∙ z≡x))
... | no _ = here y≡z
pf-keep {x} {y} {Γ = z ∷ Γ} (there yIn) neq with z ≟pf x
... | yes _ = pf-keep yIn neq
... | no _ = there (pf-keep yIn neq)

subset-swap-mid-pf :
  ∀ (Σ Δ : Ctx) (c d Aα : PFormula)
  → ((Σ ++ [ c ] ++ [ d ] ++ Δ) -pf Aα)
      ⊆
    ((Σ ++ [ d ] ++ [ c ] ++ Δ) -pf Aα)
subset-swap-mid-pf Σ Δ c d Aα = solveCtx⊆!

subset-add-dup-head-pf :
  ∀ (x Aα : PFormula) (Γ : Ctx)
  → ((x ∷ Γ) -pf Aα) ⊆ ((x ∷ x ∷ Γ) -pf Aα)
subset-add-dup-head-pf x Aα Γ = solveCtx⊆!

subset-drop-dup-head-pf :
  ∀ (x Aα : PFormula) (Γ : Ctx)
  → ((x ∷ x ∷ Γ) -pf Aα) ⊆ ((x ∷ Γ) -pf Aα)
subset-drop-dup-head-pf x Aα Γ = solveCtx⊆!

subset-absorb-right : ∀ {Γ₁ Γ₂ : Ctx} → Γ₂ ⊆ Γ₁ → (Γ₁ ++ Γ₂) ⊆ Γ₁
subset-absorb-right {Γ₁} sub {y} yIn with ∈-++⁻ Γ₁ yIn
... | inl yInL = yInL
... | inr yInR = sub yInR

subset-absorb-left : ∀ {Γ₁ Γ₂ : Ctx} → Γ₁ ⊆ Γ₂ → (Γ₁ ++ Γ₂) ⊆ Γ₂
subset-absorb-left {Γ₁} sub {y} yIn with ∈-++⁻ Γ₁ yIn
... | inl yInL = sub yInL
... | inr yInR = yInR

removeAll-head-subset : ∀ (Γ : Ctx) (φ : PFormula) → ((φ ∷ Γ) -pf φ) ⊆ Γ
removeAll-head-subset Γ φ {y} yIn
  with pf-remove-mem {x = φ} {y = y} {Γ = φ ∷ Γ} yIn
... | here eq , neq = ⊥.elim (neq (sym eq))
... | there yInΓ , neq = yInΓ

removeAll-mid-subset : ∀ (Δ₁ Δ₂ : Ctx) (φ : PFormula)
  → ((Δ₁ ++ (φ ∷ Δ₂)) -pf φ) ⊆ (Δ₁ ++ Δ₂)
removeAll-mid-subset Δ₁ Δ₂ φ {y} yIn
  with pf-remove-mem {x = φ} {y = y} {Γ = Δ₁ ++ (φ ∷ Δ₂)} yIn
... | yInOrig , neq with ∈-++⁻ Δ₁ yInOrig
... | inl yInΔ₁ = ∈-++⁺ˡ yInΔ₁
... | inr yInφΔ₂ with yInφΔ₂
... | here eq = ⊥.elim (neq (sym eq))
... | there yInΔ₂ = ∈-++⁺ʳ Δ₁ yInΔ₂

pf-cons-eq-raw : ∀ {φ ψ : PFormula} {Γ : Ctx}
  → φ ≡ ψ → ((ψ ∷ Γ) -pf φ) ≡ (Γ -pf φ)
pf-cons-eq-raw {φ} {ψ} {Γ} eq = pf-cons-eq {φ = φ} {ψ = ψ} {Γ = Γ} (sym eq)

init-right-tail-after-cons :
  ∀ {Γ Δ : Ctx} {A B : Formula} {α β : Position} {pf : PFormula}
  → pf ∈ (Δ -pf (A ^ α))
  → α ⊑ PFormula.pos pf
  → α ∈Init (Γ ++ (((B ^ β) ∷ Δ) -pf (A ^ α)))
init-right-tail-after-cons {Γ} {Δ} {A} {B} {α} {β} {pf} mΔ p =
  ∈Init-++⁺ʳ Γ (pf , mNew , p)
  where
    remInfo = pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = Δ} mΔ
    yInΔ : pf ∈ Δ
    yInΔ = fst remInfo
    y≠A : Neg (pf ≡ (A ^ α))
    y≠A q = snd remInfo (sym q)
    mNew : pf ∈ (((B ^ β) ∷ Δ) -pf (A ^ α))
    mNew =
      pf-keep
        {x = (A ^ α)} {y = pf} {Γ = (B ^ β) ∷ Δ}
        (there yInΔ)
        y≠A

prefix-step-right : (α : Position) (x : Token) → α ⊑ (α ∘ [ x ])
prefix-step-right α x = ⊑-++ α [ x ]

prefix-from-◃ : ∀ {α β : Position} → α ◃ β → α ⊑ β
prefix-from-◃ {α} {β} (x , eq) =
  subst (α ⊑_) (sym eq) (prefix-step-right α x)

modalConstraint-prefix-K :
  ∀ {β γ Γ Δ}
  → modalConstraint K β γ Γ Δ
  → β ⊑ γ
modalConstraint-prefix-K (step , h) = prefix-from-◃ step

modalConstraint-prefix-K4 :
  ∀ {β γ Γ Δ}
  → modalConstraint K4 β γ Γ Δ
  → β ⊑ γ
modalConstraint-prefix-K4 (step , h) = fst step

------------------------------------------------------------------------
-- Ax base-case subset lemmas (paper case 1 / case 2).

ax-left-ant-sub-inl : ∀ {y : PFormula}
  → (Γ₂ : Ctx) (Aα : PFormula)
  → y ∈ Γ₂
  → y ∈ ([ Aα ] ++ ((Γ₂ ++ [ Aα ]) -pf Aα))
ax-left-ant-sub-inl {y} Γ₂ Aα yInΓ₂ with y ≟pf Aα
... | yes y≡A = ∈-++⁺ˡ (subst (_∈ [ Aα ]) (sym y≡A) ∈-here)
... | no y≢A = ∈-++⁺ʳ [ Aα ] (pf-keep (∈-++⁺ˡ yInΓ₂) y≢A)

ax-right-succ-sub-inr : ∀ {y : PFormula}
  → (Δ₁ : Ctx) (Aα : PFormula)
  → y ∈ Δ₁
  → y ∈ ((([ Aα ] ++ Δ₁) -pf Aα) ++ [ Aα ])
ax-right-succ-sub-inr {y} Δ₁ Aα yInΔ₁ with y ≟pf Aα
... | yes y≡A =
  ∈-++⁺ʳ (([ Aα ] ++ Δ₁) -pf Aα)
    (subst (_∈ [ Aα ]) (sym y≡A) ∈-here)
... | no y≢A =
  ∈-++⁺ˡ (pf-keep (∈-++⁺ʳ [ Aα ] yInΔ₁) y≢A)

ax-right-succ-sub-inl : ∀ {y : PFormula}
  → (Δ₁ : Ctx) (Aα : PFormula)
  → y ∈ [ Aα ]
  → y ∈ ((([ Aα ] ++ Δ₁) -pf Aα) ++ [ Aα ])
ax-right-succ-sub-inl Δ₁ Aα (here y≡A) =
  ∈-++⁺ʳ (([ Aα ] ++ Δ₁) -pf Aα)
    (subst (_∈ [ Aα ]) (sym y≡A) ∈-here)
ax-right-succ-sub-inl Δ₁ Aα (there ())

ax-left-ant-sub : (Γ₂ : Ctx) (Aα : PFormula)
  → (Γ₂ ++ [ Aα ]) ⊆ ([ Aα ] ++ ((Γ₂ ++ [ Aα ]) -pf Aα))
ax-left-ant-sub Γ₂ Aα {y} yIn with ∈-++⁻ Γ₂ yIn
... | inl yInΓ₂ = ax-left-ant-sub-inl Γ₂ Aα yInΓ₂
... | inr yInA with yInA
... | here y≡A = ∈-++⁺ˡ (subst (_∈ [ Aα ]) (sym y≡A) ∈-here)
... | there ()

ax-right-succ-sub : (Δ₁ : Ctx) (Aα : PFormula)
  → ([ Aα ] ++ Δ₁) ⊆ ((([ Aα ] ++ Δ₁) -pf Aα) ++ [ Aα ])
ax-right-succ-sub Δ₁ Aα {y} yIn with ∈-++⁻ [ Aα ] yIn
... | inl yInA = ax-right-succ-sub-inl Δ₁ Aα yInA
... | inr yInΔ₁ = ax-right-succ-sub-inr Δ₁ Aα yInΔ₁

------------------------------------------------------------------------
-- Concrete Ax/Ax-side mix helpers (already used by later full Mix proof).

mix-ax-left :
  ∀ {Γ₂ Δ₂ : Ctx} {A : Formula} {α : Position}
  → (n : ℕ)
  → (Π₂ : (Γ₂ ++ [ (A ^ α) ]) ⊢ Δ₂)
  → δ Π₂ ≤ n
  → Σ (([ (A ^ α) ] ++ ((Γ₂ ++ [ (A ^ α) ]) -pf (A ^ α)))
      ⊢ ((([ (A ^ α) ] -pf (A ^ α)) ++ Δ₂)))
      (λ Π₀ → δ Π₀ ≤ n)
mix-ax-left {Γ₂} {Δ₂} {A} {α} n Π₂ δΠ₂≤n =
  let
    Π₀ : ([ (A ^ α) ] ++ ((Γ₂ ++ [ (A ^ α) ]) -pf (A ^ α)))
       ⊢ ((([ (A ^ α) ] -pf (A ^ α)) ++ Δ₂))
    Π₀ = structural
      (ax-left-ant-sub Γ₂ (A ^ α))
      (λ {x} xIn → ∈-++⁺ʳ (([ (A ^ α) ] -pf (A ^ α))) xIn)
      Π₂

    δΠ₀≤n : δ Π₀ ≤ n
    δΠ₀≤n =
      snd (structural-δ _ _ Π₂ δΠ₂≤n)
  in Π₀ , δΠ₀≤n

mix-ax-right :
  ∀ {Γ₁ Δ₁ : Ctx} {A : Formula} {α : Position}
  → (n : ℕ)
  → (Π₁ : Γ₁ ⊢ ([ (A ^ α) ] ++ Δ₁))
  → δ Π₁ ≤ n
  → Σ ((Γ₁ ++ ([ (A ^ α) ] -pf (A ^ α)))
      ⊢ (((( [ (A ^ α) ] ++ Δ₁) -pf (A ^ α)) ++ [ (A ^ α) ]))
      )
      (λ Π₀ → δ Π₀ ≤ n)
mix-ax-right {Γ₁} {Δ₁} {A} {α} n Π₁ δΠ₁≤n =
  let
    Π₀ : (Γ₁ ++ ([ (A ^ α) ] -pf (A ^ α)))
       ⊢ (((( [ (A ^ α) ] ++ Δ₁) -pf (A ^ α)) ++ [ (A ^ α) ]))
    Π₀ = structural
      (λ {x} xIn → ∈-++⁺ˡ xIn)
      (ax-right-succ-sub Δ₁ (A ^ α))
      Π₁

    δΠ₀≤n : δ Π₀ ≤ n
    δΠ₀≤n =
      snd (structural-δ _ _ Π₁ δΠ₁≤n)
  in Π₀ , δΠ₀≤n

------------------------------------------------------------------------
-- General Ax branches for the recursive Mix.

subset-head-remove-eq : ∀ {Aα Bβ : PFormula}
  → (Γ : Ctx)
  → Aα ≡ Bβ
  → Γ ⊆ ([ Bβ ] ++ (Γ -pf Aα))
subset-head-remove-eq {Aα} {Bβ} Γ eqAB {y} yIn with y ≟pf Aα
... | yes y≡A =
  ∈-++⁺ˡ
    (subst (_∈ [ Bβ ]) (sym (y≡A ∙ eqAB)) ∈-here)
... | no y≢A =
  ∈-++⁺ʳ [ Bβ ] (pf-keep yIn y≢A)

subset-remove-tail-eq : ∀ {Aα Bβ : PFormula}
  → (Δ : Ctx)
  → Aα ≡ Bβ
  → Δ ⊆ ((Δ -pf Aα) ++ [ Bβ ])
subset-remove-tail-eq {Aα} {Bβ} Δ eqAB {y} yIn with y ≟pf Aα
... | yes y≡A =
  ∈-++⁺ʳ (Δ -pf Aα)
    (subst (_∈ [ Bβ ]) (sym (y≡A ∙ eqAB)) ∈-here)
... | no y≢A =
  ∈-++⁺ˡ (pf-keep yIn y≢A)

mix-ax-left-general :
  ∀ {Γ' Δ'} {A B : Formula} {α β : Position}
  → (n : ℕ)
  → Dec ((A ^ α) ≡ (B ^ β))
  → (Π' : Γ' ⊢ Δ')
  → δ Π' ≤ n
  → Σ (([ (B ^ β) ] ++ (Γ' -pf (A ^ α)))
      ⊢ ((([ (B ^ β) ] -pf (A ^ α)) ++ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)
mix-ax-left-general {Γ'} {Δ'} {A} {B} {α} {β} n (yes eqAB) Π' δΠ'≤n =
  let
    Π₀ : ([ (B ^ β) ] ++ (Γ' -pf (A ^ α)))
       ⊢ ((([ (B ^ β) ] -pf (A ^ α)) ++ Δ'))
    Π₀ = structural
      (subset-head-remove-eq Γ' eqAB)
      (λ {x} xIn → ∈-++⁺ʳ ([ (B ^ β) ] -pf (A ^ α)) xIn)
      Π'

    δΠ₀≤n : δ Π₀ ≤ n
    δΠ₀≤n =
      snd (structural-δ _ _ Π' δΠ'≤n)
  in Π₀ , δΠ₀≤n

mix-ax-left-general {Γ'} {Δ'} {A} {B} {α} {β} n (no neqAB) Π' δΠ'≤n =
  let
    eqSingle : ([ (B ^ β) ] -pf (A ^ α)) ≡ [ (B ^ β) ]
    eqSingle = pf-singleton-neq neqAB

    subL : [ (B ^ β) ] ⊆ ([ (B ^ β) ] ++ (Γ' -pf (A ^ α)))
    subL {x} xIn = ∈-++⁺ˡ xIn

    subR : [ (B ^ β) ] ⊆ ((([ (B ^ β) ] -pf (A ^ α)) ++ Δ'))
    subR {x} xIn =
      ∈-++⁺ˡ (subst (λ ys → x ∈ ys) (sym eqSingle) xIn)

    Π₀ : ([ (B ^ β) ] ++ (Γ' -pf (A ^ α)))
       ⊢ ((([ (B ^ β) ] -pf (A ^ α)) ++ Δ'))
    Π₀ = structural subL subR (Ax {A = B} {α = β})
  in Π₀ , snd (structural-δ subL subR (Ax {A = B} {α = β}) zero-≤)

mix-ax-right-general :
  ∀ {Γ Δ} {A B : Formula} {α β : Position}
  → (n : ℕ)
  → Dec ((A ^ α) ≡ (B ^ β))
  → (Π : Γ ⊢ Δ)
  → δ Π ≤ n
  → Σ ((Γ ++ ([ (B ^ β) ] -pf (A ^ α)))
      ⊢ (((Δ -pf (A ^ α)) ++ [ (B ^ β) ]))
      )
      (λ Π₀ → δ Π₀ ≤ n)
mix-ax-right-general {Γ} {Δ} {A} {B} {α} {β} n (yes eqAB) Π δΠ≤n =
  let
    Π₀ : (Γ ++ ([ (B ^ β) ] -pf (A ^ α)))
       ⊢ (((Δ -pf (A ^ α)) ++ [ (B ^ β) ]))
    Π₀ = structural
      (λ {x} xIn → ∈-++⁺ˡ xIn)
      (subset-remove-tail-eq Δ eqAB)
      Π

    δΠ₀≤n : δ Π₀ ≤ n
    δΠ₀≤n =
      snd (structural-δ _ _ Π δΠ≤n)
  in Π₀ , δΠ₀≤n

mix-ax-right-general {Γ} {Δ} {A} {B} {α} {β} n (no neqAB) Π δΠ≤n =
  let
    eqSingle : ([ (B ^ β) ] -pf (A ^ α)) ≡ [ (B ^ β) ]
    eqSingle = pf-singleton-neq neqAB

    subL : [ (B ^ β) ] ⊆ (Γ ++ ([ (B ^ β) ] -pf (A ^ α)))
    subL {x} xIn =
      ∈-++⁺ʳ Γ (subst (λ ys → x ∈ ys) (sym eqSingle) xIn)

    subR : [ (B ^ β) ] ⊆ ((Δ -pf (A ^ α)) ++ [ (B ^ β) ])
    subR {x} xIn =
      ∈-++⁺ʳ (Δ -pf (A ^ α)) xIn

    Π₀ : (Γ ++ ([ (B ^ β) ] -pf (A ^ α)))
       ⊢ (((Δ -pf (A ^ α)) ++ [ (B ^ β) ]))
    Π₀ = structural subL subR (Ax {A = B} {α = β})
  in Π₀ , snd (structural-δ subL subR (Ax {A = B} {α = β}) zero-≤)

mix-left-Ax :
  ∀ {Γ' Δ'} {A B : Formula} {α β : Position}
  → (n : ℕ)
  → (Π' : Γ' ⊢ Δ')
  → δ Π' ≤ n
  → Σ (([ (B ^ β) ] ++ (Γ' -pf (A ^ α)))
      ⊢ ((([ (B ^ β) ] -pf (A ^ α)) ++ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)
mix-left-Ax {A = A} {B = B} {α = α} {β = β} n Π' δΠ'≤n =
  mix-ax-left-general n ((A ^ α) ≟pf (B ^ β)) Π' δΠ'≤n

mix-right-Ax :
  ∀ {Γ Δ} {A B : Formula} {α β : Position}
  → (n : ℕ)
  → (Π : Γ ⊢ Δ)
  → δ Π ≤ n
  → Σ ((Γ ++ ([ (B ^ β) ] -pf (A ^ α)))
      ⊢ (((Δ -pf (A ^ α)) ++ [ (B ^ β) ]))
      )
      (λ Π₀ → δ Π₀ ≤ n)
mix-right-Ax {A = A} {B = B} {α = α} {β = β} n Π δΠ≤n =
  mix-ax-right-general n ((A ^ α) ≟pf (B ^ β)) Π δΠ≤n

MixResult :
  (n : ℕ)
  {Γ Δ Γ' Δ' : Ctx} {A : Formula} {α : Position}
  → Type
MixResult n {Γ} {Δ} {Γ'} {Δ'} {A} {α} =
  Σ ((Γ ++ (Γ' -pf (A ^ α)))
    ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
    (λ Π₀ → δ Π₀ ≤ n)

liftMixResult : ∀ {m n : ℕ} {Γ Δ Γ' Δ' : Ctx} {A : Formula} {α : Position}
  → m ≤ n → MixResult m {Γ} {Δ} {Γ'} {Δ'} {A} {α}
  → MixResult n {Γ} {Δ} {Γ'} {Δ'} {A} {α}
liftMixResult m≤n (Π₀ , bound) = Π₀ , ≤-trans bound m≤n

------------------------------------------------------------------------
-- cutConstraint transport for structural recursion in mix.

∈Init-subset : ∀ {t Γ Δ}
  → Γ ⊆ Δ
  → t ∈Init Γ
  → t ∈Init Δ
∈Init-subset sub (pf , m , p) = pf , sub m , p

cutConstraint-down-left-WeakenL-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint m A α ((C ^ γ) ∷ Γ) Γ' Δ Δ'
  → Maybe (cutConstraint m A α Γ Γ' Δ Δ')
cutConstraint-down-left-WeakenL-gen K {Γ} {A = A} {C = C} {α = α} {γ = γ} c with c
... | inr w = just (inr w)
... | inl w with ∈Init-++⁻ ((C ^ γ) ∷ Γ) w
...   | inr wTail = just (inl (∈Init-++⁺ʳ Γ wTail))
...   | inl (pf , here _ , p) = nothing
...   | inl (pf , there mΓ , p) = just (inl (∈Init-++⁺ˡ (pf , mΓ , p)))
cutConstraint-down-left-WeakenL-gen K4 {Γ} {A = A} {C = C} {α = α} {γ = γ} c with c
... | inr w = just (inr w)
... | inl w with ∈Init-++⁻ ((C ^ γ) ∷ Γ) w
...   | inr wTail = just (inl (∈Init-++⁺ʳ Γ wTail))
...   | inl (pf , here _ , p) = nothing
...   | inl (pf , there mΓ , p) = just (inl (∈Init-++⁺ˡ (pf , mΓ , p)))
cutConstraint-down-left-WeakenL-gen D c = just tt
cutConstraint-down-left-WeakenL-gen T c = just tt
cutConstraint-down-left-WeakenL-gen D4 c = just tt
cutConstraint-down-left-WeakenL-gen S4 c = just tt
cutConstraint-down-left-WeakenL-gen S4dot2 c = just tt
cutConstraint-down-left-WeakenL-gen S5 c = just tt

cutConstraint-down-left-WeakenL :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint M A α ((C ^ γ) ∷ Γ) Γ' Δ Δ'
  → Maybe (cutConstraint M A α Γ Γ' Δ Δ')
cutConstraint-down-left-WeakenL = cutConstraint-down-left-WeakenL-gen M

cutConstraint-down-left-WeakenR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint m A α Γ Γ' ((C ^ γ) ∷ Δ) Δ'
  → Maybe (cutConstraint m A α Γ Γ' Δ Δ')
cutConstraint-down-left-WeakenR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr w) = just (inr w)
cutConstraint-down-left-WeakenR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ = just (inl (∈Init-++⁺ˡ wΓ))
... | inr wRem with (C ^ γ) ≟pf (A ^ α)
...   | yes c≡a =
      just (inl (∈Init-++⁺ʳ Γ wRem))
...   | no c≢a with wRem
...     | pf , here _ , p = nothing
...     | pf , there mΔ , p = just (inl (∈Init-++⁺ʳ Γ (pf , mΔ , p)))
cutConstraint-down-left-WeakenR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr w) = just (inr w)
cutConstraint-down-left-WeakenR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ = just (inl (∈Init-++⁺ˡ wΓ))
... | inr wRem with (C ^ γ) ≟pf (A ^ α)
...   | yes c≡a =
      just (inl (∈Init-++⁺ʳ Γ wRem))
...   | no c≢a with wRem
...     | pf , here _ , p = nothing
...     | pf , there mΔ , p = just (inl (∈Init-++⁺ʳ Γ (pf , mΔ , p)))
cutConstraint-down-left-WeakenR-gen D c = just tt
cutConstraint-down-left-WeakenR-gen T c = just tt
cutConstraint-down-left-WeakenR-gen D4 c = just tt
cutConstraint-down-left-WeakenR-gen S4 c = just tt
cutConstraint-down-left-WeakenR-gen S4dot2 c = just tt
cutConstraint-down-left-WeakenR-gen S5 c = just tt

cutConstraint-down-left-WeakenR :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint M A α Γ Γ' ((C ^ γ) ∷ Δ) Δ'
  → Maybe (cutConstraint M A α Γ Γ' Δ Δ')
cutConstraint-down-left-WeakenR = cutConstraint-down-left-WeakenR-gen M

cutConstraint-down-left-NotL-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → cutConstraint m A α ((Not B ^ β) ∷ Γ) Γ' Δ Δ'
  → Maybe (cutConstraint m A α Γ Γ' ((B ^ β) ∷ Δ) Δ')
cutConstraint-down-left-NotL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inr w) = just (inr w)
cutConstraint-down-left-NotL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ ((Not B ^ β) ∷ Γ) w
... | inl (pf , here pf≡head , pαpf) =
  headCase ((B ^ β) ≟pf (A ^ α))
  where
    pαβ : α ⊑ β
    pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡head) pαpf

    headCase : Dec ((B ^ β) ≡ (A ^ α))
      → Maybe (cutConstraint K A α Γ Γ' ((B ^ β) ∷ Δ) Δ')
    headCase (yes _) = nothing
    headCase (no b≢a) =
      just (inl (subst (α ∈Init_) eqCtx wHead))
      where
        eqRem : (((B ^ β) ∷ Δ) -pf (A ^ α))
             ≡ ((B ^ β) ∷ (Δ -pf (A ^ α)))
        eqRem =
          pf-cons-neq
            {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ}
            (λ q → b≢a (sym q))

        eqCtx : Γ ++ ((B ^ β) ∷ (Δ -pf (A ^ α)))
            ≡ Γ ++ (((B ^ β) ∷ Δ) -pf (A ^ α))
        eqCtx = cong (Γ ++_) (sym eqRem)

        wHead : α ∈Init (Γ ++ ((B ^ β) ∷ (Δ -pf (A ^ α))))
        wHead = ∈Init-++⁺ʳ Γ ((B ^ β) , here refl , pαβ)
... | inl (pf , there mΓ , p) = just (inl (∈Init-++⁺ˡ (pf , mΓ , p)))
... | inr (pf , mΔ , p) =
    just (inl (init-right-tail-after-cons {Γ = Γ} {Δ = Δ}
      {A = A} {B = B} {α = α} {β = β} {pf = pf} mΔ p))
cutConstraint-down-left-NotL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inr w) = just (inr w)
cutConstraint-down-left-NotL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ ((Not B ^ β) ∷ Γ) w
... | inl (pf , here pf≡head , pαpf) =
  headCase ((B ^ β) ≟pf (A ^ α))
  where
    pαβ : α ⊑ β
    pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡head) pαpf

    headCase : Dec ((B ^ β) ≡ (A ^ α))
      → Maybe (cutConstraint K4 A α Γ Γ' ((B ^ β) ∷ Δ) Δ')
    headCase (yes _) = nothing
    headCase (no b≢a) =
      just (inl (subst (α ∈Init_) eqCtx wHead))
      where
        eqRem : (((B ^ β) ∷ Δ) -pf (A ^ α))
             ≡ ((B ^ β) ∷ (Δ -pf (A ^ α)))
        eqRem =
          pf-cons-neq
            {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ}
            (λ q → b≢a (sym q))

        eqCtx : Γ ++ ((B ^ β) ∷ (Δ -pf (A ^ α)))
            ≡ Γ ++ (((B ^ β) ∷ Δ) -pf (A ^ α))
        eqCtx = cong (Γ ++_) (sym eqRem)

        wHead : α ∈Init (Γ ++ ((B ^ β) ∷ (Δ -pf (A ^ α))))
        wHead = ∈Init-++⁺ʳ Γ ((B ^ β) , here refl , pαβ)
... | inl (pf , there mΓ , p) = just (inl (∈Init-++⁺ˡ (pf , mΓ , p)))
... | inr (pf , mΔ , p) =
    just (inl (init-right-tail-after-cons {Γ = Γ} {Δ = Δ}
      {A = A} {B = B} {α = α} {β = β} {pf = pf} mΔ p))
cutConstraint-down-left-NotL-gen D c = just tt
cutConstraint-down-left-NotL-gen T c = just tt
cutConstraint-down-left-NotL-gen D4 c = just tt
cutConstraint-down-left-NotL-gen S4 c = just tt
cutConstraint-down-left-NotL-gen S4dot2 c = just tt
cutConstraint-down-left-NotL-gen S5 c = just tt

cutConstraint-down-left-NotL :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → cutConstraint M A α ((Not B ^ β) ∷ Γ) Γ' Δ Δ'
  → Maybe (cutConstraint M A α Γ Γ' ((B ^ β) ∷ Δ) Δ')
cutConstraint-down-left-NotL = cutConstraint-down-left-NotL-gen M

cutConstraint-down-left-NotR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → cutConstraint m A α Γ Γ' ((Not B ^ β) ∷ Δ) Δ'
  → cutConstraint m A α ((B ^ β) ∷ Γ) Γ' Δ Δ'
cutConstraint-down-left-NotR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inr w) = inr w
cutConstraint-down-left-NotR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ =
    inl
      (∈Init-++⁺ˡ
        {Γ = (B ^ β) ∷ Γ}
        {Δ = (Δ -pf (A ^ α))}
        (∈Init-∷ (B ^ β) wΓ))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (Not B ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡notB =
        inl
          (∈Init-++⁺ˡ
            {Γ = (B ^ β) ∷ Γ}
            {Δ = (Δ -pf (A ^ α))}
            ((B ^ β) ,
              here refl ,
              subst (λ z → α ⊑ z) (cong PFormula.pos pf≡notB) p))
...     | there yInΔ =
        inl
          (∈Init-++⁺ʳ ((B ^ β) ∷ Γ)
            (pf ,
              pf-keep
                {x = (A ^ α)} {y = pf} {Γ = Δ}
                yInΔ (λ q → y≠A (sym q)) ,
              p))
cutConstraint-down-left-NotR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inr w) = inr w
cutConstraint-down-left-NotR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ =
    inl
      (∈Init-++⁺ˡ
        {Γ = (B ^ β) ∷ Γ}
        {Δ = (Δ -pf (A ^ α))}
        (∈Init-∷ (B ^ β) wΓ))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (Not B ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡notB =
        inl
          (∈Init-++⁺ˡ
            {Γ = (B ^ β) ∷ Γ}
            {Δ = (Δ -pf (A ^ α))}
            ((B ^ β) ,
              here refl ,
              subst (λ z → α ⊑ z) (cong PFormula.pos pf≡notB) p))
...     | there yInΔ =
        inl
          (∈Init-++⁺ʳ ((B ^ β) ∷ Γ)
            (pf ,
              pf-keep
                {x = (A ^ α)} {y = pf} {Γ = Δ}
                yInΔ (λ q → y≠A (sym q)) ,
              p))
cutConstraint-down-left-NotR-gen D c = tt
cutConstraint-down-left-NotR-gen T c = tt
cutConstraint-down-left-NotR-gen D4 c = tt
cutConstraint-down-left-NotR-gen S4 c = tt
cutConstraint-down-left-NotR-gen S4dot2 c = tt
cutConstraint-down-left-NotR-gen S5 c = tt

cutConstraint-down-left-NotR :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → cutConstraint M A α Γ Γ' ((Not B ^ β) ∷ Δ) Δ'
  → cutConstraint M A α ((B ^ β) ∷ Γ) Γ' Δ Δ'
cutConstraint-down-left-NotR = cutConstraint-down-left-NotR-gen M

cutConstraint-down-left-AndL1-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α ((And B C ^ β) ∷ Γ) Γ' Δ Δ'
  → cutConstraint m A α ((B ^ β) ∷ Γ) Γ' Δ Δ'
cutConstraint-down-left-AndL1-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = inr w
cutConstraint-down-left-AndL1-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ ((And B C ^ β) ∷ Γ) w
... | inr wRem = inl (∈Init-++⁺ʳ ((B ^ β) ∷ Γ) wRem)
... | inl (pf , here pf≡and , p) =
    inl
      (∈Init-++⁺ˡ
        {Γ = (B ^ β) ∷ Γ}
        {Δ = (Δ -pf (A ^ α))}
        ((B ^ β) ,
          here refl ,
          subst (λ z → α ⊑ z) (cong PFormula.pos pf≡and) p))
... | inl (pf , there mΓ , p) =
    inl
      (∈Init-++⁺ˡ
        {Γ = (B ^ β) ∷ Γ}
        {Δ = (Δ -pf (A ^ α))}
        (pf , there mΓ , p))
cutConstraint-down-left-AndL1-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = inr w
cutConstraint-down-left-AndL1-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ ((And B C ^ β) ∷ Γ) w
... | inr wRem = inl (∈Init-++⁺ʳ ((B ^ β) ∷ Γ) wRem)
... | inl (pf , here pf≡and , p) =
    inl
      (∈Init-++⁺ˡ
        {Γ = (B ^ β) ∷ Γ}
        {Δ = (Δ -pf (A ^ α))}
        ((B ^ β) ,
          here refl ,
          subst (λ z → α ⊑ z) (cong PFormula.pos pf≡and) p))
... | inl (pf , there mΓ , p) =
    inl
      (∈Init-++⁺ˡ
        {Γ = (B ^ β) ∷ Γ}
        {Δ = (Δ -pf (A ^ α))}
        (pf , there mΓ , p))
cutConstraint-down-left-AndL1-gen D c = tt
cutConstraint-down-left-AndL1-gen T c = tt
cutConstraint-down-left-AndL1-gen D4 c = tt
cutConstraint-down-left-AndL1-gen S4 c = tt
cutConstraint-down-left-AndL1-gen S4dot2 c = tt
cutConstraint-down-left-AndL1-gen S5 c = tt

cutConstraint-down-left-AndL1 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α ((And B C ^ β) ∷ Γ) Γ' Δ Δ'
  → cutConstraint M A α ((B ^ β) ∷ Γ) Γ' Δ Δ'
cutConstraint-down-left-AndL1 = cutConstraint-down-left-AndL1-gen M

cutConstraint-down-left-AndL2-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α ((And B C ^ β) ∷ Γ) Γ' Δ Δ'
  → cutConstraint m A α ((C ^ β) ∷ Γ) Γ' Δ Δ'
cutConstraint-down-left-AndL2-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = inr w
cutConstraint-down-left-AndL2-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ ((And B C ^ β) ∷ Γ) w
... | inr wRem = inl (∈Init-++⁺ʳ ((C ^ β) ∷ Γ) wRem)
... | inl (pf , here pf≡and , p) =
    inl
      (∈Init-++⁺ˡ
        {Γ = (C ^ β) ∷ Γ}
        {Δ = (Δ -pf (A ^ α))}
        ((C ^ β) ,
          here refl ,
          subst (λ z → α ⊑ z) (cong PFormula.pos pf≡and) p))
... | inl (pf , there mΓ , p) =
    inl
      (∈Init-++⁺ˡ
        {Γ = (C ^ β) ∷ Γ}
        {Δ = (Δ -pf (A ^ α))}
        (pf , there mΓ , p))
cutConstraint-down-left-AndL2-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = inr w
cutConstraint-down-left-AndL2-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ ((And B C ^ β) ∷ Γ) w
... | inr wRem = inl (∈Init-++⁺ʳ ((C ^ β) ∷ Γ) wRem)
... | inl (pf , here pf≡and , p) =
    inl
      (∈Init-++⁺ˡ
        {Γ = (C ^ β) ∷ Γ}
        {Δ = (Δ -pf (A ^ α))}
        ((C ^ β) ,
          here refl ,
          subst (λ z → α ⊑ z) (cong PFormula.pos pf≡and) p))
... | inl (pf , there mΓ , p) =
    inl
      (∈Init-++⁺ˡ
        {Γ = (C ^ β) ∷ Γ}
        {Δ = (Δ -pf (A ^ α))}
        (pf , there mΓ , p))
cutConstraint-down-left-AndL2-gen D c = tt
cutConstraint-down-left-AndL2-gen T c = tt
cutConstraint-down-left-AndL2-gen D4 c = tt
cutConstraint-down-left-AndL2-gen S4 c = tt
cutConstraint-down-left-AndL2-gen S4dot2 c = tt
cutConstraint-down-left-AndL2-gen S5 c = tt

cutConstraint-down-left-AndL2 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α ((And B C ^ β) ∷ Γ) Γ' Δ Δ'
  → cutConstraint M A α ((C ^ β) ∷ Γ) Γ' Δ Δ'
cutConstraint-down-left-AndL2 = cutConstraint-down-left-AndL2-gen M

cutConstraint-down-left-OrR1-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ Γ' ((Or B C ^ β) ∷ Δ) Δ'
  → Maybe (cutConstraint m A α Γ Γ' ((B ^ β) ∷ Δ) Δ')
cutConstraint-down-left-OrR1-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = just (inr w)
cutConstraint-down-left-OrR1-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ = just (inl (∈Init-++⁺ˡ wΓ))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (Or B C ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡or =
        headCase ((B ^ β) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡or) p

          headCase : Dec ((B ^ β) ≡ (A ^ α))
            → Maybe (cutConstraint K A α Γ Γ' ((B ^ β) ∷ Δ) Δ')
          headCase (yes _) = nothing
          headCase (no b≢a) =
            just (inl (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((B ^ β) ∷ Δ) -pf (A ^ α))
                   ≡ ((B ^ β) ∷ (Δ -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ}
                  (λ q → b≢a (sym q))

              eqCtx : Γ ++ ((B ^ β) ∷ (Δ -pf (A ^ α)))
                  ≡ Γ ++ (((B ^ β) ∷ Δ) -pf (A ^ α))
              eqCtx = cong (Γ ++_) (sym eqRem)

              wHead : α ∈Init (Γ ++ ((B ^ β) ∷ (Δ -pf (A ^ α))))
              wHead = ∈Init-++⁺ʳ Γ ((B ^ β) , here refl , pαβ)
...     | there yInΔ =
        just
          (inl
            (init-right-tail-after-cons
              {Γ = Γ} {Δ = Δ} {A = A} {B = B} {α = α} {β = β}
              {pf = pf}
              mΔ p))
      where
        mΔ : pf ∈ (Δ -pf (A ^ α))
        mΔ = pf-keep yInΔ (λ q → y≠A (sym q))
cutConstraint-down-left-OrR1-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = just (inr w)
cutConstraint-down-left-OrR1-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ = just (inl (∈Init-++⁺ˡ wΓ))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (Or B C ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡or =
        headCase ((B ^ β) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡or) p

          headCase : Dec ((B ^ β) ≡ (A ^ α))
            → Maybe (cutConstraint K4 A α Γ Γ' ((B ^ β) ∷ Δ) Δ')
          headCase (yes _) = nothing
          headCase (no b≢a) =
            just (inl (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((B ^ β) ∷ Δ) -pf (A ^ α))
                   ≡ ((B ^ β) ∷ (Δ -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ}
                  (λ q → b≢a (sym q))

              eqCtx : Γ ++ ((B ^ β) ∷ (Δ -pf (A ^ α)))
                  ≡ Γ ++ (((B ^ β) ∷ Δ) -pf (A ^ α))
              eqCtx = cong (Γ ++_) (sym eqRem)

              wHead : α ∈Init (Γ ++ ((B ^ β) ∷ (Δ -pf (A ^ α))))
              wHead = ∈Init-++⁺ʳ Γ ((B ^ β) , here refl , pαβ)
...     | there yInΔ =
        just
          (inl
            (init-right-tail-after-cons
              {Γ = Γ} {Δ = Δ} {A = A} {B = B} {α = α} {β = β}
              {pf = pf}
              mΔ p))
      where
        mΔ : pf ∈ (Δ -pf (A ^ α))
        mΔ = pf-keep yInΔ (λ q → y≠A (sym q))
cutConstraint-down-left-OrR1-gen D c = just tt
cutConstraint-down-left-OrR1-gen T c = just tt
cutConstraint-down-left-OrR1-gen D4 c = just tt
cutConstraint-down-left-OrR1-gen S4 c = just tt
cutConstraint-down-left-OrR1-gen S4dot2 c = just tt
cutConstraint-down-left-OrR1-gen S5 c = just tt

cutConstraint-down-left-OrR1 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ Γ' ((Or B C ^ β) ∷ Δ) Δ'
  → Maybe (cutConstraint M A α Γ Γ' ((B ^ β) ∷ Δ) Δ')
cutConstraint-down-left-OrR1 = cutConstraint-down-left-OrR1-gen M

cutConstraint-down-left-OrR2-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ Γ' ((Or B C ^ β) ∷ Δ) Δ'
  → Maybe (cutConstraint m A α Γ Γ' ((C ^ β) ∷ Δ) Δ')
cutConstraint-down-left-OrR2-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = just (inr w)
cutConstraint-down-left-OrR2-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ = just (inl (∈Init-++⁺ˡ wΓ))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (Or B C ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡or =
        headCase ((C ^ β) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡or) p

          headCase : Dec ((C ^ β) ≡ (A ^ α))
            → Maybe (cutConstraint K A α Γ Γ' ((C ^ β) ∷ Δ) Δ')
          headCase (yes _) = nothing
          headCase (no c≢a) =
            just (inl (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((C ^ β) ∷ Δ) -pf (A ^ α))
                   ≡ ((C ^ β) ∷ (Δ -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Δ}
                  (λ q → c≢a (sym q))

              eqCtx : Γ ++ ((C ^ β) ∷ (Δ -pf (A ^ α)))
                  ≡ Γ ++ (((C ^ β) ∷ Δ) -pf (A ^ α))
              eqCtx = cong (Γ ++_) (sym eqRem)

              wHead : α ∈Init (Γ ++ ((C ^ β) ∷ (Δ -pf (A ^ α))))
              wHead = ∈Init-++⁺ʳ Γ ((C ^ β) , here refl , pαβ)
...     | there yInΔ =
        just
          (inl
            (init-right-tail-after-cons
              {Γ = Γ} {Δ = Δ} {A = A} {B = C} {α = α} {β = β}
              {pf = pf}
              mΔ p))
      where
        mΔ : pf ∈ (Δ -pf (A ^ α))
        mΔ = pf-keep yInΔ (λ q → y≠A (sym q))
cutConstraint-down-left-OrR2-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = just (inr w)
cutConstraint-down-left-OrR2-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ = just (inl (∈Init-++⁺ˡ wΓ))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (Or B C ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡or =
        headCase ((C ^ β) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡or) p

          headCase : Dec ((C ^ β) ≡ (A ^ α))
            → Maybe (cutConstraint K4 A α Γ Γ' ((C ^ β) ∷ Δ) Δ')
          headCase (yes _) = nothing
          headCase (no c≢a) =
            just (inl (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((C ^ β) ∷ Δ) -pf (A ^ α))
                   ≡ ((C ^ β) ∷ (Δ -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Δ}
                  (λ q → c≢a (sym q))

              eqCtx : Γ ++ ((C ^ β) ∷ (Δ -pf (A ^ α)))
                  ≡ Γ ++ (((C ^ β) ∷ Δ) -pf (A ^ α))
              eqCtx = cong (Γ ++_) (sym eqRem)

              wHead : α ∈Init (Γ ++ ((C ^ β) ∷ (Δ -pf (A ^ α))))
              wHead = ∈Init-++⁺ʳ Γ ((C ^ β) , here refl , pαβ)
...     | there yInΔ =
        just
          (inl
            (init-right-tail-after-cons
              {Γ = Γ} {Δ = Δ} {A = A} {B = C} {α = α} {β = β}
              {pf = pf}
              mΔ p))
      where
        mΔ : pf ∈ (Δ -pf (A ^ α))
        mΔ = pf-keep yInΔ (λ q → y≠A (sym q))
cutConstraint-down-left-OrR2-gen D c = just tt
cutConstraint-down-left-OrR2-gen T c = just tt
cutConstraint-down-left-OrR2-gen D4 c = just tt
cutConstraint-down-left-OrR2-gen S4 c = just tt
cutConstraint-down-left-OrR2-gen S4dot2 c = just tt
cutConstraint-down-left-OrR2-gen S5 c = just tt

cutConstraint-down-left-OrR2 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ Γ' ((Or B C ^ β) ∷ Δ) Δ'
  → Maybe (cutConstraint M A α Γ Γ' ((C ^ β) ∷ Δ) Δ')
cutConstraint-down-left-OrR2 = cutConstraint-down-left-OrR2-gen M

cutConstraint-down-left-ImpR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ Γ' (((B ⇒ C) ^ β) ∷ Δ) Δ'
  → Maybe (cutConstraint m A α ((B ^ β) ∷ Γ) Γ' ((C ^ β) ∷ Δ) Δ')
cutConstraint-down-left-ImpR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = just (inr w)
cutConstraint-down-left-ImpR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ =
    just
      (inl
        (∈Init-++⁺ˡ
          {Γ = (B ^ β) ∷ Γ}
          {Δ = (((C ^ β) ∷ Δ) -pf (A ^ α))}
          (∈Init-∷ (B ^ β) wΓ)))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = ((B ⇒ C) ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡imp =
        headCase ((C ^ β) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡imp) p

          headCase : Dec ((C ^ β) ≡ (A ^ α))
            → Maybe (cutConstraint K A α ((B ^ β) ∷ Γ) Γ' ((C ^ β) ∷ Δ) Δ')
          headCase (yes _) = nothing
          headCase (no c≢a) =
            just (inl (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((C ^ β) ∷ Δ) -pf (A ^ α))
                   ≡ ((C ^ β) ∷ (Δ -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Δ}
                  (λ q → c≢a (sym q))

              eqCtx : ((B ^ β) ∷ Γ) ++ ((C ^ β) ∷ (Δ -pf (A ^ α)))
                  ≡ ((B ^ β) ∷ Γ) ++ (((C ^ β) ∷ Δ) -pf (A ^ α))
              eqCtx = cong (((B ^ β) ∷ Γ) ++_) (sym eqRem)

              wHead : α ∈Init (((B ^ β) ∷ Γ) ++ ((C ^ β) ∷ (Δ -pf (A ^ α))))
              wHead = ∈Init-++⁺ʳ ((B ^ β) ∷ Γ) ((C ^ β) , here refl , pαβ)
...     | there yInΔ =
        just
          (inl
            (init-right-tail-after-cons
              {Γ = (B ^ β) ∷ Γ} {Δ = Δ} {A = A} {B = C} {α = α} {β = β}
              {pf = pf}
              mΔ p))
      where
        mΔ : pf ∈ (Δ -pf (A ^ α))
        mΔ = pf-keep yInΔ (λ q → y≠A (sym q))
cutConstraint-down-left-ImpR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = just (inr w)
cutConstraint-down-left-ImpR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ =
    just
      (inl
        (∈Init-++⁺ˡ
          {Γ = (B ^ β) ∷ Γ}
          {Δ = (((C ^ β) ∷ Δ) -pf (A ^ α))}
          (∈Init-∷ (B ^ β) wΓ)))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = ((B ⇒ C) ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡imp =
        headCase ((C ^ β) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡imp) p

          headCase : Dec ((C ^ β) ≡ (A ^ α))
            → Maybe (cutConstraint K4 A α ((B ^ β) ∷ Γ) Γ' ((C ^ β) ∷ Δ) Δ')
          headCase (yes _) = nothing
          headCase (no c≢a) =
            just (inl (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((C ^ β) ∷ Δ) -pf (A ^ α))
                   ≡ ((C ^ β) ∷ (Δ -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Δ}
                  (λ q → c≢a (sym q))

              eqCtx : ((B ^ β) ∷ Γ) ++ ((C ^ β) ∷ (Δ -pf (A ^ α)))
                  ≡ ((B ^ β) ∷ Γ) ++ (((C ^ β) ∷ Δ) -pf (A ^ α))
              eqCtx = cong (((B ^ β) ∷ Γ) ++_) (sym eqRem)

              wHead : α ∈Init (((B ^ β) ∷ Γ) ++ ((C ^ β) ∷ (Δ -pf (A ^ α))))
              wHead = ∈Init-++⁺ʳ ((B ^ β) ∷ Γ) ((C ^ β) , here refl , pαβ)
...     | there yInΔ =
        just
          (inl
            (init-right-tail-after-cons
              {Γ = (B ^ β) ∷ Γ} {Δ = Δ} {A = A} {B = C} {α = α} {β = β}
              {pf = pf}
              mΔ p))
      where
        mΔ : pf ∈ (Δ -pf (A ^ α))
        mΔ = pf-keep yInΔ (λ q → y≠A (sym q))
cutConstraint-down-left-ImpR-gen D c = just tt
cutConstraint-down-left-ImpR-gen T c = just tt
cutConstraint-down-left-ImpR-gen D4 c = just tt
cutConstraint-down-left-ImpR-gen S4 c = just tt
cutConstraint-down-left-ImpR-gen S4dot2 c = just tt
cutConstraint-down-left-ImpR-gen S5 c = just tt

cutConstraint-down-left-ImpR :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ Γ' (((B ⇒ C) ^ β) ∷ Δ) Δ'
  → Maybe (cutConstraint M A α ((B ^ β) ∷ Γ) Γ' ((C ^ β) ∷ Δ) Δ')
cutConstraint-down-left-ImpR = cutConstraint-down-left-ImpR-gen M

cutConstraint-down-left-BoxR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position} {x : Token}
  → cutConstraint m A α Γ Γ' ((□ B ^ β) ∷ Δ) Δ'
  → Maybe (cutConstraint m A α Γ Γ' ((B ^ (β ∘ [ x ])) ∷ Δ) Δ')
cutConstraint-down-left-BoxR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inr w) = just (inr w)
cutConstraint-down-left-BoxR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ = just (inl (∈Init-++⁺ˡ wΓ))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (□ B ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡box =
        headCase ((B ^ (β ∘ [ x ])) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡box) p

          pαβx : α ⊑ (β ∘ [ x ])
          pαβx = ⊑-trans pαβ (prefix-step-right β x)

          headCase : Dec ((B ^ (β ∘ [ x ])) ≡ (A ^ α))
            → Maybe (cutConstraint K A α Γ Γ' ((B ^ (β ∘ [ x ])) ∷ Δ) Δ')
          headCase (yes _) = nothing
          headCase (no b≢a) =
            just (inl (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((B ^ (β ∘ [ x ])) ∷ Δ) -pf (A ^ α))
                   ≡ ((B ^ (β ∘ [ x ])) ∷ (Δ -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ (β ∘ [ x ]))} {Γ = Δ}
                  (λ q → b≢a (sym q))

              eqCtx : Γ ++ ((B ^ (β ∘ [ x ])) ∷ (Δ -pf (A ^ α)))
                  ≡ Γ ++ (((B ^ (β ∘ [ x ])) ∷ Δ) -pf (A ^ α))
              eqCtx = cong (Γ ++_) (sym eqRem)

              wHead : α ∈Init (Γ ++ ((B ^ (β ∘ [ x ])) ∷ (Δ -pf (A ^ α))))
              wHead = ∈Init-++⁺ʳ Γ ((B ^ (β ∘ [ x ])) , here refl , pαβx)
...     | there yInΔ =
        just
          (inl
            (init-right-tail-after-cons
              {Γ = Γ} {Δ = Δ} {A = A} {B = B} {α = α} {β = (β ∘ [ x ])}
              {pf = pf}
              mΔ p))
      where
        mΔ : pf ∈ (Δ -pf (A ^ α))
        mΔ = pf-keep yInΔ (λ q → y≠A (sym q))
cutConstraint-down-left-BoxR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inr w) = just (inr w)
cutConstraint-down-left-BoxR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ = just (inl (∈Init-++⁺ˡ wΓ))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (□ B ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡box =
        headCase ((B ^ (β ∘ [ x ])) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡box) p

          pαβx : α ⊑ (β ∘ [ x ])
          pαβx = ⊑-trans pαβ (prefix-step-right β x)

          headCase : Dec ((B ^ (β ∘ [ x ])) ≡ (A ^ α))
            → Maybe (cutConstraint K4 A α Γ Γ' ((B ^ (β ∘ [ x ])) ∷ Δ) Δ')
          headCase (yes _) = nothing
          headCase (no b≢a) =
            just (inl (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((B ^ (β ∘ [ x ])) ∷ Δ) -pf (A ^ α))
                   ≡ ((B ^ (β ∘ [ x ])) ∷ (Δ -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ (β ∘ [ x ]))} {Γ = Δ}
                  (λ q → b≢a (sym q))

              eqCtx : Γ ++ ((B ^ (β ∘ [ x ])) ∷ (Δ -pf (A ^ α)))
                  ≡ Γ ++ (((B ^ (β ∘ [ x ])) ∷ Δ) -pf (A ^ α))
              eqCtx = cong (Γ ++_) (sym eqRem)

              wHead : α ∈Init (Γ ++ ((B ^ (β ∘ [ x ])) ∷ (Δ -pf (A ^ α))))
              wHead = ∈Init-++⁺ʳ Γ ((B ^ (β ∘ [ x ])) , here refl , pαβx)
...     | there yInΔ =
        just
          (inl
            (init-right-tail-after-cons
              {Γ = Γ} {Δ = Δ} {A = A} {B = B} {α = α} {β = (β ∘ [ x ])}
              {pf = pf}
              mΔ p))
      where
        mΔ : pf ∈ (Δ -pf (A ^ α))
        mΔ = pf-keep yInΔ (λ q → y≠A (sym q))
cutConstraint-down-left-BoxR-gen D c = just tt
cutConstraint-down-left-BoxR-gen T c = just tt
cutConstraint-down-left-BoxR-gen D4 c = just tt
cutConstraint-down-left-BoxR-gen S4 c = just tt
cutConstraint-down-left-BoxR-gen S4dot2 c = just tt
cutConstraint-down-left-BoxR-gen S5 c = just tt

cutConstraint-down-left-BoxR :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position} {x : Token}
  → cutConstraint M A α Γ Γ' ((□ B ^ β) ∷ Δ) Δ'
  → Maybe (cutConstraint M A α Γ Γ' ((B ^ (β ∘ [ x ])) ∷ Δ) Δ')
cutConstraint-down-left-BoxR = cutConstraint-down-left-BoxR-gen M

cutConstraint-down-left-DiaL-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position} {x : Token}
  → cutConstraint m A α (Γ ++ [ ♢ B ^ β ]) Γ' Δ Δ'
  → cutConstraint m A α (Γ ++ [ B ^ (β ∘ [ x ]) ]) Γ' Δ Δ'
cutConstraint-down-left-DiaL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inr w) = inr w
cutConstraint-down-left-DiaL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inl w) with ∈Init-++⁻ (Γ ++ [ ♢ B ^ β ]) w
... | inr wTail = inl (∈Init-++⁺ʳ (Γ ++ [ B ^ (β ∘ [ x ]) ]) wTail)
... | inl wAnt with ∈Init-++⁻ Γ wAnt
...   | inl wΓ = inl (∈Init-++⁺ˡ (∈Init-++⁺ˡ wΓ))
...   | inr (pf , mSingle , p) with mSingle
...     | here pf≡dia =
      inl (∈Init-++⁺ˡ (∈Init-++⁺ʳ Γ ((B ^ (β ∘ [ x ])) , here refl , pαβx)))
      where
        pαβ : α ⊑ β
        pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡dia) p

        pαβx : α ⊑ (β ∘ [ x ])
        pαβx = ⊑-trans pαβ (prefix-step-right β x)
...     | there ()
cutConstraint-down-left-DiaL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inr w) = inr w
cutConstraint-down-left-DiaL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inl w) with ∈Init-++⁻ (Γ ++ [ ♢ B ^ β ]) w
... | inr wTail = inl (∈Init-++⁺ʳ (Γ ++ [ B ^ (β ∘ [ x ]) ]) wTail)
... | inl wAnt with ∈Init-++⁻ Γ wAnt
...   | inl wΓ = inl (∈Init-++⁺ˡ (∈Init-++⁺ˡ wΓ))
...   | inr (pf , mSingle , p) with mSingle
...     | here pf≡dia =
      inl (∈Init-++⁺ˡ (∈Init-++⁺ʳ Γ ((B ^ (β ∘ [ x ])) , here refl , pαβx)))
      where
        pαβ : α ⊑ β
        pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡dia) p

        pαβx : α ⊑ (β ∘ [ x ])
        pαβx = ⊑-trans pαβ (prefix-step-right β x)
...     | there ()
cutConstraint-down-left-DiaL-gen D c = tt
cutConstraint-down-left-DiaL-gen T c = tt
cutConstraint-down-left-DiaL-gen D4 c = tt
cutConstraint-down-left-DiaL-gen S4 c = tt
cutConstraint-down-left-DiaL-gen S4dot2 c = tt
cutConstraint-down-left-DiaL-gen S5 c = tt

cutConstraint-down-left-DiaL :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position} {x : Token}
  → cutConstraint M A α (Γ ++ [ ♢ B ^ β ]) Γ' Δ Δ'
  → cutConstraint M A α (Γ ++ [ B ^ (β ∘ [ x ]) ]) Γ' Δ Δ'
cutConstraint-down-left-DiaL = cutConstraint-down-left-DiaL-gen M

cutConstraint-down-left-BoxL-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → modalConstraint m β γ Γ Δ
  → cutConstraint m A α (Γ ++ [ □ B ^ β ]) Γ' Δ Δ'
  → cutConstraint m A α (Γ ++ [ B ^ γ ]) Γ' Δ Δ'
cutConstraint-down-left-BoxL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inr w) = inr w
cutConstraint-down-left-BoxL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inl w) with ∈Init-++⁻ (Γ ++ [ □ B ^ β ]) w
... | inr wTail = inl (∈Init-++⁺ʳ (Γ ++ [ B ^ γ ]) wTail)
... | inl wAnt with ∈Init-++⁻ Γ wAnt
...   | inl wΓ = inl (∈Init-++⁺ˡ (∈Init-++⁺ˡ wΓ))
...   | inr (pf , mSingle , p) with mSingle
...     | here pf≡box =
      inl (∈Init-++⁺ˡ (∈Init-++⁺ʳ Γ ((B ^ γ) , here refl , pαγ)))
      where
        pαβ : α ⊑ β
        pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡box) p

        pβγ : β ⊑ γ
        pβγ = modalConstraint-prefix-K {β = β} {γ = γ} {Γ = Γ} {Δ = Δ} mc

        pαγ : α ⊑ γ
        pαγ = ⊑-trans pαβ pβγ
...     | there ()
cutConstraint-down-left-BoxL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inr w) = inr w
cutConstraint-down-left-BoxL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inl w) with ∈Init-++⁻ (Γ ++ [ □ B ^ β ]) w
... | inr wTail = inl (∈Init-++⁺ʳ (Γ ++ [ B ^ γ ]) wTail)
... | inl wAnt with ∈Init-++⁻ Γ wAnt
...   | inl wΓ = inl (∈Init-++⁺ˡ (∈Init-++⁺ˡ wΓ))
...   | inr (pf , mSingle , p) with mSingle
...     | here pf≡box =
      inl (∈Init-++⁺ˡ (∈Init-++⁺ʳ Γ ((B ^ γ) , here refl , pαγ)))
      where
        pαβ : α ⊑ β
        pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡box) p

        pβγ : β ⊑ γ
        pβγ = modalConstraint-prefix-K4 {β = β} {γ = γ} {Γ = Γ} {Δ = Δ} mc

        pαγ : α ⊑ γ
        pαγ = ⊑-trans pαβ pβγ
...     | there ()
cutConstraint-down-left-BoxL-gen D mc c = tt
cutConstraint-down-left-BoxL-gen T mc c = tt
cutConstraint-down-left-BoxL-gen D4 mc c = tt
cutConstraint-down-left-BoxL-gen S4 mc c = tt
cutConstraint-down-left-BoxL-gen S4dot2 mc c = tt
cutConstraint-down-left-BoxL-gen S5 mc c = tt

cutConstraint-down-left-BoxL :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → modalConstraint M β γ Γ Δ
  → cutConstraint M A α (Γ ++ [ □ B ^ β ]) Γ' Δ Δ'
  → cutConstraint M A α (Γ ++ [ B ^ γ ]) Γ' Δ Δ'
cutConstraint-down-left-BoxL = cutConstraint-down-left-BoxL-gen M

cutConstraint-down-left-DiaR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → modalConstraint m β γ Γ Δ
  → cutConstraint m A α Γ Γ' ((♢ B ^ β) ∷ Δ) Δ'
  → Maybe (cutConstraint m A α Γ Γ' ((B ^ γ) ∷ Δ) Δ')
cutConstraint-down-left-DiaR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inr w) = just (inr w)
cutConstraint-down-left-DiaR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ = just (inl (∈Init-++⁺ˡ wΓ))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (♢ B ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡dia =
        headCase ((B ^ γ) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡dia) p

          pβγ : β ⊑ γ
          pβγ = modalConstraint-prefix-K {β = β} {γ = γ} {Γ = Γ} {Δ = Δ} mc

          pαγ : α ⊑ γ
          pαγ = ⊑-trans pαβ pβγ

          headCase : Dec ((B ^ γ) ≡ (A ^ α))
            → Maybe (cutConstraint K A α Γ Γ' ((B ^ γ) ∷ Δ) Δ')
          headCase (yes _) = nothing
          headCase (no b≢a) =
            just (inl (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((B ^ γ) ∷ Δ) -pf (A ^ α))
                   ≡ ((B ^ γ) ∷ (Δ -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ γ)} {Γ = Δ}
                  (λ q → b≢a (sym q))

              eqCtx : Γ ++ ((B ^ γ) ∷ (Δ -pf (A ^ α)))
                  ≡ Γ ++ (((B ^ γ) ∷ Δ) -pf (A ^ α))
              eqCtx = cong (Γ ++_) (sym eqRem)

              wHead : α ∈Init (Γ ++ ((B ^ γ) ∷ (Δ -pf (A ^ α))))
              wHead = ∈Init-++⁺ʳ Γ ((B ^ γ) , here refl , pαγ)
...     | there yInΔ =
        just
          (inl
            (init-right-tail-after-cons
              {Γ = Γ} {Δ = Δ} {A = A} {B = B} {α = α} {β = γ}
              {pf = pf}
              mΔ p))
      where
        mΔ : pf ∈ (Δ -pf (A ^ α))
        mΔ = pf-keep yInΔ (λ q → y≠A (sym q))
cutConstraint-down-left-DiaR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inr w) = just (inr w)
cutConstraint-down-left-DiaR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inl w) with ∈Init-++⁻ Γ w
... | inl wΓ = just (inl (∈Init-++⁺ˡ wΓ))
... | inr (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (♢ B ^ β) ∷ Δ} mRem
...   | yInOrig , y≠A with yInOrig
...     | here pf≡dia =
        headCase ((B ^ γ) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡dia) p

          pβγ : β ⊑ γ
          pβγ = modalConstraint-prefix-K4 {β = β} {γ = γ} {Γ = Γ} {Δ = Δ} mc

          pαγ : α ⊑ γ
          pαγ = ⊑-trans pαβ pβγ

          headCase : Dec ((B ^ γ) ≡ (A ^ α))
            → Maybe (cutConstraint K4 A α Γ Γ' ((B ^ γ) ∷ Δ) Δ')
          headCase (yes _) = nothing
          headCase (no b≢a) =
            just (inl (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((B ^ γ) ∷ Δ) -pf (A ^ α))
                   ≡ ((B ^ γ) ∷ (Δ -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ γ)} {Γ = Δ}
                  (λ q → b≢a (sym q))

              eqCtx : Γ ++ ((B ^ γ) ∷ (Δ -pf (A ^ α)))
                  ≡ Γ ++ (((B ^ γ) ∷ Δ) -pf (A ^ α))
              eqCtx = cong (Γ ++_) (sym eqRem)

              wHead : α ∈Init (Γ ++ ((B ^ γ) ∷ (Δ -pf (A ^ α))))
              wHead = ∈Init-++⁺ʳ Γ ((B ^ γ) , here refl , pαγ)
...     | there yInΔ =
        just
          (inl
            (init-right-tail-after-cons
              {Γ = Γ} {Δ = Δ} {A = A} {B = B} {α = α} {β = γ}
              {pf = pf}
              mΔ p))
      where
        mΔ : pf ∈ (Δ -pf (A ^ α))
        mΔ = pf-keep yInΔ (λ q → y≠A (sym q))
cutConstraint-down-left-DiaR-gen D mc c = just tt
cutConstraint-down-left-DiaR-gen T mc c = just tt
cutConstraint-down-left-DiaR-gen D4 mc c = just tt
cutConstraint-down-left-DiaR-gen S4 mc c = just tt
cutConstraint-down-left-DiaR-gen S4dot2 mc c = just tt
cutConstraint-down-left-DiaR-gen S5 mc c = just tt

cutConstraint-down-left-DiaR :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → modalConstraint M β γ Γ Δ
  → cutConstraint M A α Γ Γ' ((♢ B ^ β) ∷ Δ) Δ'
  → Maybe (cutConstraint M A α Γ Γ' ((B ^ γ) ∷ Δ) Δ')
cutConstraint-down-left-DiaR = cutConstraint-down-left-DiaR-gen M

cutConstraint-down-right-WeakenL-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint m A α Γ ((C ^ γ) ∷ Γ') Δ Δ'
  → Maybe (cutConstraint m A α Γ Γ' Δ Δ')
cutConstraint-down-right-WeakenL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) = just (inl w)
cutConstraint-down-right-WeakenL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr w) with (C ^ γ) ≟pf (A ^ α)
... | yes c≡a =
  just (inr w)
... | no c≢a with ∈Init-++⁻ ((C ^ γ) ∷ (Γ' -pf (A ^ α))) w
...   | inr wΔ' = just (inr (∈Init-++⁺ʳ (Γ' -pf (A ^ α)) wΔ'))
...   | inl (pf , here _ , p) = nothing
...   | inl (pf , there mΓ' , p) = just (inr (∈Init-++⁺ˡ (pf , mΓ' , p)))
cutConstraint-down-right-WeakenL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) = just (inl w)
cutConstraint-down-right-WeakenL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr w) with (C ^ γ) ≟pf (A ^ α)
... | yes c≡a =
  just (inr w)
... | no c≢a with ∈Init-++⁻ ((C ^ γ) ∷ (Γ' -pf (A ^ α))) w
...   | inr wΔ' = just (inr (∈Init-++⁺ʳ (Γ' -pf (A ^ α)) wΔ'))
...   | inl (pf , here _ , p) = nothing
...   | inl (pf , there mΓ' , p) = just (inr (∈Init-++⁺ˡ (pf , mΓ' , p)))
cutConstraint-down-right-WeakenL-gen D c = just tt
cutConstraint-down-right-WeakenL-gen T c = just tt
cutConstraint-down-right-WeakenL-gen D4 c = just tt
cutConstraint-down-right-WeakenL-gen S4 c = just tt
cutConstraint-down-right-WeakenL-gen S4dot2 c = just tt
cutConstraint-down-right-WeakenL-gen S5 c = just tt

cutConstraint-down-right-WeakenL :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint M A α Γ ((C ^ γ) ∷ Γ') Δ Δ'
  → Maybe (cutConstraint M A α Γ Γ' Δ Δ')
cutConstraint-down-right-WeakenL = cutConstraint-down-right-WeakenL-gen M

cutConstraint-up-right-ContractL-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint m A α Γ ((C ^ γ) ∷ Γ') Δ Δ'
  → cutConstraint m A α Γ ((C ^ γ) ∷ (C ^ γ) ∷ Γ') Δ Δ'
cutConstraint-up-right-ContractL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) = inl w
cutConstraint-up-right-ContractL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr w) = inr (∈Init-subset sub w)
  where
    sub : ((((C ^ γ) ∷ Γ') -pf (A ^ α)) ++ Δ')
       ⊆ (((((C ^ γ) ∷ (C ^ γ) ∷ Γ') -pf (A ^ α)) ++ Δ'))
    sub = solveCtx⊆!
cutConstraint-up-right-ContractL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) = inl w
cutConstraint-up-right-ContractL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr w) = inr (∈Init-subset sub w)
  where
    sub : ((((C ^ γ) ∷ Γ') -pf (A ^ α)) ++ Δ')
       ⊆ (((((C ^ γ) ∷ (C ^ γ) ∷ Γ') -pf (A ^ α)) ++ Δ'))
    sub = solveCtx⊆!
cutConstraint-up-right-ContractL-gen D c = tt
cutConstraint-up-right-ContractL-gen T c = tt
cutConstraint-up-right-ContractL-gen D4 c = tt
cutConstraint-up-right-ContractL-gen S4 c = tt
cutConstraint-up-right-ContractL-gen S4dot2 c = tt
cutConstraint-up-right-ContractL-gen S5 c = tt

cutConstraint-up-right-ContractL :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint M A α Γ ((C ^ γ) ∷ Γ') Δ Δ'
  → cutConstraint M A α Γ ((C ^ γ) ∷ (C ^ γ) ∷ Γ') Δ Δ'
cutConstraint-up-right-ContractL = cutConstraint-up-right-ContractL-gen M

cutConstraint-up-left-ContractL-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint m A α ((C ^ γ) ∷ Γ) Γ' Δ Δ'
  → cutConstraint m A α ((C ^ γ) ∷ (C ^ γ) ∷ Γ) Γ' Δ Δ'
cutConstraint-up-left-ContractL-gen K {C = C} {γ = γ} c with c
... | inl w = inl (∈Init-∷ (C ^ γ) w)
... | inr w = inr w
cutConstraint-up-left-ContractL-gen K4 {C = C} {γ = γ} c with c
... | inl w = inl (∈Init-∷ (C ^ γ) w)
... | inr w = inr w
cutConstraint-up-left-ContractL-gen D c = tt
cutConstraint-up-left-ContractL-gen T c = tt
cutConstraint-up-left-ContractL-gen D4 c = tt
cutConstraint-up-left-ContractL-gen S4 c = tt
cutConstraint-up-left-ContractL-gen S4dot2 c = tt
cutConstraint-up-left-ContractL-gen S5 c = tt

cutConstraint-up-left-ContractL :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint M A α ((C ^ γ) ∷ Γ) Γ' Δ Δ'
  → cutConstraint M A α ((C ^ γ) ∷ (C ^ γ) ∷ Γ) Γ' Δ Δ'
cutConstraint-up-left-ContractL = cutConstraint-up-left-ContractL-gen M

cutConstraint-up-left-ContractR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint m A α Γ Γ' ((C ^ γ) ∷ Δ) Δ'
  → cutConstraint m A α Γ Γ' ((C ^ γ) ∷ (C ^ γ) ∷ Δ) Δ'
cutConstraint-up-left-ContractR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) = inl (∈Init-subset sub w)
  where
    sub : (Γ ++ (((C ^ γ) ∷ Δ) -pf (A ^ α)))
       ⊆ (Γ ++ (((C ^ γ) ∷ (C ^ γ) ∷ Δ) -pf (A ^ α)))
    sub = solveCtx⊆!
cutConstraint-up-left-ContractR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr w) = inr w
cutConstraint-up-left-ContractR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) = inl (∈Init-subset sub w)
  where
    sub : (Γ ++ (((C ^ γ) ∷ Δ) -pf (A ^ α)))
       ⊆ (Γ ++ (((C ^ γ) ∷ (C ^ γ) ∷ Δ) -pf (A ^ α)))
    sub = solveCtx⊆!
cutConstraint-up-left-ContractR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr w) = inr w
cutConstraint-up-left-ContractR-gen D c = tt
cutConstraint-up-left-ContractR-gen T c = tt
cutConstraint-up-left-ContractR-gen D4 c = tt
cutConstraint-up-left-ContractR-gen S4 c = tt
cutConstraint-up-left-ContractR-gen S4dot2 c = tt
cutConstraint-up-left-ContractR-gen S5 c = tt

cutConstraint-up-left-ContractR :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint M A α Γ Γ' ((C ^ γ) ∷ Δ) Δ'
  → cutConstraint M A α Γ Γ' ((C ^ γ) ∷ (C ^ γ) ∷ Δ) Δ'
cutConstraint-up-left-ContractR = cutConstraint-up-left-ContractR-gen M

cutConstraint-up-right-WeakenR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint m A α Γ Γ' Δ Δ'
  → cutConstraint m A α Γ Γ' Δ ((C ^ γ) ∷ Δ')
cutConstraint-up-right-WeakenR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) = inl w
cutConstraint-up-right-WeakenR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr w) =
  inr (∈Init-subset
        (subset-append-right-cons (Γ' -pf (A ^ α)) Δ' (C ^ γ))
        w)
cutConstraint-up-right-WeakenR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) = inl w
cutConstraint-up-right-WeakenR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr w) =
  inr (∈Init-subset
        (subset-append-right-cons (Γ' -pf (A ^ α)) Δ' (C ^ γ))
        w)
cutConstraint-up-right-WeakenR-gen D c = tt
cutConstraint-up-right-WeakenR-gen T c = tt
cutConstraint-up-right-WeakenR-gen D4 c = tt
cutConstraint-up-right-WeakenR-gen S4 c = tt
cutConstraint-up-right-WeakenR-gen S4dot2 c = tt
cutConstraint-up-right-WeakenR-gen S5 c = tt

cutConstraint-up-right-WeakenR :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint M A α Γ Γ' Δ Δ'
  → cutConstraint M A α Γ Γ' Δ ((C ^ γ) ∷ Δ')
cutConstraint-up-right-WeakenR = cutConstraint-up-right-WeakenR-gen M

cutConstraint-down-right-WeakenR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint m A α Γ Γ' Δ ((C ^ γ) ∷ Δ')
  → Maybe (cutConstraint m A α Γ Γ' Δ Δ')
cutConstraint-down-right-WeakenR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) = just (inl w)
cutConstraint-down-right-WeakenR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr (pf , m , p)) with ∈-++⁻ (Γ' -pf (A ^ α)) m
... | inl mΓ = just (inr (pf , ∈-++⁺ˡ mΓ , p))
... | inr (here _) = nothing
... | inr (there mΔ') = just (inr (pf , ∈-++⁺ʳ (Γ' -pf (A ^ α)) mΔ' , p))
cutConstraint-down-right-WeakenR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inl w) = just (inl w)
cutConstraint-down-right-WeakenR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {C = C} {α = α} {γ = γ}
  (inr (pf , m , p)) with ∈-++⁻ (Γ' -pf (A ^ α)) m
... | inl mΓ = just (inr (pf , ∈-++⁺ˡ mΓ , p))
... | inr (here _) = nothing
... | inr (there mΔ') = just (inr (pf , ∈-++⁺ʳ (Γ' -pf (A ^ α)) mΔ' , p))
cutConstraint-down-right-WeakenR-gen D c = just tt
cutConstraint-down-right-WeakenR-gen T c = just tt
cutConstraint-down-right-WeakenR-gen D4 c = just tt
cutConstraint-down-right-WeakenR-gen S4 c = just tt
cutConstraint-down-right-WeakenR-gen S4dot2 c = just tt
cutConstraint-down-right-WeakenR-gen S5 c = just tt

cutConstraint-down-right-WeakenR :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint M A α Γ Γ' Δ ((C ^ γ) ∷ Δ')
  → Maybe (cutConstraint M A α Γ Γ' Δ Δ')
cutConstraint-down-right-WeakenR = cutConstraint-down-right-WeakenR-gen M

cutConstraint-down-right-NotL-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → cutConstraint m A α Γ ((Not B ^ β) ∷ Γ') Δ Δ'
  → Maybe (cutConstraint m A α Γ Γ' Δ ((B ^ β) ∷ Δ'))
cutConstraint-down-right-NotL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-NotL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inr w) = branch (∈Init-++⁻ (((Not B ^ β) ∷ Γ') -pf (A ^ α)) w)
  where
    branch :
      (α ∈Init (((Not B ^ β) ∷ Γ') -pf (A ^ α)))
      ⊎
      (α ∈Init Δ')
      → Maybe (cutConstraint K A α Γ Γ' Δ ((B ^ β) ∷ Δ'))

    branch (inr (pf , mΔ' , p)) =
      just
        (inr
          (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
            (pf , there mΔ' , p)))

    branch (inl (pf , mΓRem , p))
      with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (Not B ^ β) ∷ Γ'} mΓRem
    ... | yInOrig , y≠A with yInOrig
    ...   | here pf≡notB =
        just
          (inr
            (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
              ((B ^ β) ,
                here refl ,
                subst (λ z → α ⊑ z) (cong PFormula.pos pf≡notB) p)))
    ...   | there yInΓ' =
        just
          (inr
            (∈Init-++⁺ˡ
              (pf ,
                pf-keep
                  {x = (A ^ α)} {y = pf} {Γ = Γ'}
                  yInΓ' (λ q → y≠A (sym q)) ,
                p)))
cutConstraint-down-right-NotL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-NotL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inr w) = branch (∈Init-++⁻ (((Not B ^ β) ∷ Γ') -pf (A ^ α)) w)
  where
    branch :
      (α ∈Init (((Not B ^ β) ∷ Γ') -pf (A ^ α)))
      ⊎
      (α ∈Init Δ')
      → Maybe (cutConstraint K4 A α Γ Γ' Δ ((B ^ β) ∷ Δ'))

    branch (inr (pf , mΔ' , p)) =
      just
        (inr
          (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
            (pf , there mΔ' , p)))

    branch (inl (pf , mΓRem , p))
      with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (Not B ^ β) ∷ Γ'} mΓRem
    ... | yInOrig , y≠A with yInOrig
    ...   | here pf≡notB =
        just
          (inr
            (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
              ((B ^ β) ,
                here refl ,
                subst (λ z → α ⊑ z) (cong PFormula.pos pf≡notB) p)))
    ...   | there yInΓ' =
        just
          (inr
            (∈Init-++⁺ˡ
              (pf ,
                pf-keep
                  {x = (A ^ α)} {y = pf} {Γ = Γ'}
                  yInΓ' (λ q → y≠A (sym q)) ,
                p)))
cutConstraint-down-right-NotL-gen D c = just tt
cutConstraint-down-right-NotL-gen T c = just tt
cutConstraint-down-right-NotL-gen D4 c = just tt
cutConstraint-down-right-NotL-gen S4 c = just tt
cutConstraint-down-right-NotL-gen S4dot2 c = just tt
cutConstraint-down-right-NotL-gen S5 c = just tt

cutConstraint-down-right-NotL :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → cutConstraint M A α Γ ((Not B ^ β) ∷ Γ') Δ Δ'
  → Maybe (cutConstraint M A α Γ Γ' Δ ((B ^ β) ∷ Δ'))
cutConstraint-down-right-NotL = cutConstraint-down-right-NotL-gen M

cutConstraint-down-right-AndL1-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ ((And B C ^ β) ∷ Γ') Δ Δ'
  → Maybe (cutConstraint m A α Γ ((B ^ β) ∷ Γ') Δ Δ')
cutConstraint-down-right-AndL1-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-AndL1-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = branch (∈Init-++⁻ (((And B C ^ β) ∷ Γ') -pf (A ^ α)) w)
  where
    branch :
      (α ∈Init (((And B C ^ β) ∷ Γ') -pf (A ^ α)))
      ⊎
      (α ∈Init Δ')
      → Maybe (cutConstraint K A α Γ ((B ^ β) ∷ Γ') Δ Δ')

    branch (inr wΔ') =
      just (inr (∈Init-++⁺ʳ (((B ^ β) ∷ Γ') -pf (A ^ α)) wΔ'))

    branch (inl (pf , mΓRem , p))
      with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (And B C ^ β) ∷ Γ'} mΓRem
    ... | yInOrig , y≠A with yInOrig
    ...   | here pf≡and =
        headCase ((B ^ β) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡and) p

          headCase : Dec ((B ^ β) ≡ (A ^ α))
            → Maybe (cutConstraint K A α Γ ((B ^ β) ∷ Γ') Δ Δ')
          headCase (yes _) = nothing
          headCase (no b≢a) =
            just (inr (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((B ^ β) ∷ Γ') -pf (A ^ α))
                   ≡ ((B ^ β) ∷ (Γ' -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'}
                  (λ q → b≢a (sym q))

              eqCtx : ((B ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ'
                  ≡ (((B ^ β) ∷ Γ') -pf (A ^ α)) ++ Δ'
              eqCtx = cong (_++ Δ') (sym eqRem)

              wHead : α ∈Init (((B ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ')
              wHead =
                ∈Init-++⁺ˡ
                  {Γ = (B ^ β) ∷ (Γ' -pf (A ^ α))}
                  {Δ = Δ'}
                  ((B ^ β) , here refl , pαβ)
    ...   | there yInΓ' =
        just
          (inr
            (∈Init-++⁺ˡ
              (pf ,
                pf-keep
                  {x = (A ^ α)} {y = pf} {Γ = (B ^ β) ∷ Γ'}
                  (there yInΓ') (λ q → y≠A (sym q)) ,
                p)))
cutConstraint-down-right-AndL1-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-AndL1-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = branch (∈Init-++⁻ (((And B C ^ β) ∷ Γ') -pf (A ^ α)) w)
  where
    branch :
      (α ∈Init (((And B C ^ β) ∷ Γ') -pf (A ^ α)))
      ⊎
      (α ∈Init Δ')
      → Maybe (cutConstraint K4 A α Γ ((B ^ β) ∷ Γ') Δ Δ')

    branch (inr wΔ') =
      just (inr (∈Init-++⁺ʳ (((B ^ β) ∷ Γ') -pf (A ^ α)) wΔ'))

    branch (inl (pf , mΓRem , p))
      with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (And B C ^ β) ∷ Γ'} mΓRem
    ... | yInOrig , y≠A with yInOrig
    ...   | here pf≡and =
        headCase ((B ^ β) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡and) p

          headCase : Dec ((B ^ β) ≡ (A ^ α))
            → Maybe (cutConstraint K4 A α Γ ((B ^ β) ∷ Γ') Δ Δ')
          headCase (yes _) = nothing
          headCase (no b≢a) =
            just (inr (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((B ^ β) ∷ Γ') -pf (A ^ α))
                   ≡ ((B ^ β) ∷ (Γ' -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'}
                  (λ q → b≢a (sym q))

              eqCtx : ((B ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ'
                  ≡ (((B ^ β) ∷ Γ') -pf (A ^ α)) ++ Δ'
              eqCtx = cong (_++ Δ') (sym eqRem)

              wHead : α ∈Init (((B ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ')
              wHead =
                ∈Init-++⁺ˡ
                  {Γ = (B ^ β) ∷ (Γ' -pf (A ^ α))}
                  {Δ = Δ'}
                  ((B ^ β) , here refl , pαβ)
    ...   | there yInΓ' =
        just
          (inr
            (∈Init-++⁺ˡ
              (pf ,
                pf-keep
                  {x = (A ^ α)} {y = pf} {Γ = (B ^ β) ∷ Γ'}
                  (there yInΓ') (λ q → y≠A (sym q)) ,
                p)))
cutConstraint-down-right-AndL1-gen D c = just tt
cutConstraint-down-right-AndL1-gen T c = just tt
cutConstraint-down-right-AndL1-gen D4 c = just tt
cutConstraint-down-right-AndL1-gen S4 c = just tt
cutConstraint-down-right-AndL1-gen S4dot2 c = just tt
cutConstraint-down-right-AndL1-gen S5 c = just tt

cutConstraint-down-right-AndL1 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ ((And B C ^ β) ∷ Γ') Δ Δ'
  → Maybe (cutConstraint M A α Γ ((B ^ β) ∷ Γ') Δ Δ')
cutConstraint-down-right-AndL1 = cutConstraint-down-right-AndL1-gen M

cutConstraint-down-right-AndL2-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ ((And B C ^ β) ∷ Γ') Δ Δ'
  → Maybe (cutConstraint m A α Γ ((C ^ β) ∷ Γ') Δ Δ')
cutConstraint-down-right-AndL2-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-AndL2-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = branch (∈Init-++⁻ (((And B C ^ β) ∷ Γ') -pf (A ^ α)) w)
  where
    branch :
      (α ∈Init (((And B C ^ β) ∷ Γ') -pf (A ^ α)))
      ⊎
      (α ∈Init Δ')
      → Maybe (cutConstraint K A α Γ ((C ^ β) ∷ Γ') Δ Δ')

    branch (inr wΔ') =
      just (inr (∈Init-++⁺ʳ (((C ^ β) ∷ Γ') -pf (A ^ α)) wΔ'))

    branch (inl (pf , mΓRem , p))
      with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (And B C ^ β) ∷ Γ'} mΓRem
    ... | yInOrig , y≠A with yInOrig
    ...   | here pf≡and =
        headCase ((C ^ β) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡and) p

          headCase : Dec ((C ^ β) ≡ (A ^ α))
            → Maybe (cutConstraint K A α Γ ((C ^ β) ∷ Γ') Δ Δ')
          headCase (yes _) = nothing
          headCase (no c≢a) =
            just (inr (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((C ^ β) ∷ Γ') -pf (A ^ α))
                   ≡ ((C ^ β) ∷ (Γ' -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Γ'}
                  (λ q → c≢a (sym q))

              eqCtx : ((C ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ'
                  ≡ (((C ^ β) ∷ Γ') -pf (A ^ α)) ++ Δ'
              eqCtx = cong (_++ Δ') (sym eqRem)

              wHead : α ∈Init (((C ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ')
              wHead =
                ∈Init-++⁺ˡ
                  {Γ = (C ^ β) ∷ (Γ' -pf (A ^ α))}
                  {Δ = Δ'}
                  ((C ^ β) , here refl , pαβ)
    ...   | there yInΓ' =
        just
          (inr
            (∈Init-++⁺ˡ
              (pf ,
                pf-keep
                  {x = (A ^ α)} {y = pf} {Γ = (C ^ β) ∷ Γ'}
                  (there yInΓ') (λ q → y≠A (sym q)) ,
                p)))
cutConstraint-down-right-AndL2-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-AndL2-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) = branch (∈Init-++⁻ (((And B C ^ β) ∷ Γ') -pf (A ^ α)) w)
  where
    branch :
      (α ∈Init (((And B C ^ β) ∷ Γ') -pf (A ^ α)))
      ⊎
      (α ∈Init Δ')
      → Maybe (cutConstraint K4 A α Γ ((C ^ β) ∷ Γ') Δ Δ')

    branch (inr wΔ') =
      just (inr (∈Init-++⁺ʳ (((C ^ β) ∷ Γ') -pf (A ^ α)) wΔ'))

    branch (inl (pf , mΓRem , p))
      with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (And B C ^ β) ∷ Γ'} mΓRem
    ... | yInOrig , y≠A with yInOrig
    ...   | here pf≡and =
        headCase ((C ^ β) ≟pf (A ^ α))
        where
          pαβ : α ⊑ β
          pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡and) p

          headCase : Dec ((C ^ β) ≡ (A ^ α))
            → Maybe (cutConstraint K4 A α Γ ((C ^ β) ∷ Γ') Δ Δ')
          headCase (yes _) = nothing
          headCase (no c≢a) =
            just (inr (subst (α ∈Init_) eqCtx wHead))
            where
              eqRem : (((C ^ β) ∷ Γ') -pf (A ^ α))
                   ≡ ((C ^ β) ∷ (Γ' -pf (A ^ α)))
              eqRem =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Γ'}
                  (λ q → c≢a (sym q))

              eqCtx : ((C ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ'
                  ≡ (((C ^ β) ∷ Γ') -pf (A ^ α)) ++ Δ'
              eqCtx = cong (_++ Δ') (sym eqRem)

              wHead : α ∈Init (((C ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ')
              wHead =
                ∈Init-++⁺ˡ
                  {Γ = (C ^ β) ∷ (Γ' -pf (A ^ α))}
                  {Δ = Δ'}
                  ((C ^ β) , here refl , pαβ)
    ...   | there yInΓ' =
        just
          (inr
            (∈Init-++⁺ˡ
              (pf ,
                pf-keep
                  {x = (A ^ α)} {y = pf} {Γ = (C ^ β) ∷ Γ'}
                  (there yInΓ') (λ q → y≠A (sym q)) ,
                p)))
cutConstraint-down-right-AndL2-gen D c = just tt
cutConstraint-down-right-AndL2-gen T c = just tt
cutConstraint-down-right-AndL2-gen D4 c = just tt
cutConstraint-down-right-AndL2-gen S4 c = just tt
cutConstraint-down-right-AndL2-gen S4dot2 c = just tt
cutConstraint-down-right-AndL2-gen S5 c = just tt

cutConstraint-down-right-AndL2 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ ((And B C ^ β) ∷ Γ') Δ Δ'
  → Maybe (cutConstraint M A α Γ ((C ^ β) ∷ Γ') Δ Δ')
cutConstraint-down-right-AndL2 = cutConstraint-down-right-AndL2-gen M

cutConstraint-down-right-OrR1-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ Γ' Δ ((Or B C ^ β) ∷ Δ')
  → Maybe (cutConstraint m A α Γ Γ' Δ ((B ^ β) ∷ Δ'))
cutConstraint-down-right-OrR1-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-OrR1-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl wΓ = just (inr (∈Init-++⁺ˡ wΓ))
... | inr (pf , mTail , p) with mTail
...   | here pf≡or =
    just
      (inr
        (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
          ((B ^ β) ,
            here refl ,
            subst (λ z → α ⊑ z) (cong PFormula.pos pf≡or) p)))
...   | there mΔ' =
    just
      (inr
        (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
          (pf , there mΔ' , p)))
cutConstraint-down-right-OrR1-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-OrR1-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl wΓ = just (inr (∈Init-++⁺ˡ wΓ))
... | inr (pf , mTail , p) with mTail
...   | here pf≡or =
    just
      (inr
        (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
          ((B ^ β) ,
            here refl ,
            subst (λ z → α ⊑ z) (cong PFormula.pos pf≡or) p)))
...   | there mΔ' =
    just
      (inr
        (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
          (pf , there mΔ' , p)))
cutConstraint-down-right-OrR1-gen D c = just tt
cutConstraint-down-right-OrR1-gen T c = just tt
cutConstraint-down-right-OrR1-gen D4 c = just tt
cutConstraint-down-right-OrR1-gen S4 c = just tt
cutConstraint-down-right-OrR1-gen S4dot2 c = just tt
cutConstraint-down-right-OrR1-gen S5 c = just tt

cutConstraint-down-right-OrR1 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ Γ' Δ ((Or B C ^ β) ∷ Δ')
  → Maybe (cutConstraint M A α Γ Γ' Δ ((B ^ β) ∷ Δ'))
cutConstraint-down-right-OrR1 = cutConstraint-down-right-OrR1-gen M

cutConstraint-down-right-OrR2-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ Γ' Δ ((Or B C ^ β) ∷ Δ')
  → Maybe (cutConstraint m A α Γ Γ' Δ ((C ^ β) ∷ Δ'))
cutConstraint-down-right-OrR2-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-OrR2-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl wΓ = just (inr (∈Init-++⁺ˡ wΓ))
... | inr (pf , mTail , p) with mTail
...   | here pf≡or =
    just
      (inr
        (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
          ((C ^ β) ,
            here refl ,
            subst (λ z → α ⊑ z) (cong PFormula.pos pf≡or) p)))
...   | there mΔ' =
    just
      (inr
        (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
          (pf , there mΔ' , p)))
cutConstraint-down-right-OrR2-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-OrR2-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl wΓ = just (inr (∈Init-++⁺ˡ wΓ))
... | inr (pf , mTail , p) with mTail
...   | here pf≡or =
    just
      (inr
        (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
          ((C ^ β) ,
            here refl ,
            subst (λ z → α ⊑ z) (cong PFormula.pos pf≡or) p)))
...   | there mΔ' =
    just
      (inr
        (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
          (pf , there mΔ' , p)))
cutConstraint-down-right-OrR2-gen D c = just tt
cutConstraint-down-right-OrR2-gen T c = just tt
cutConstraint-down-right-OrR2-gen D4 c = just tt
cutConstraint-down-right-OrR2-gen S4 c = just tt
cutConstraint-down-right-OrR2-gen S4dot2 c = just tt
cutConstraint-down-right-OrR2-gen S5 c = just tt

cutConstraint-down-right-OrR2 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ Γ' Δ ((Or B C ^ β) ∷ Δ')
  → Maybe (cutConstraint M A α Γ Γ' Δ ((C ^ β) ∷ Δ'))
cutConstraint-down-right-OrR2 = cutConstraint-down-right-OrR2-gen M

cutConstraint-down-right-ImpR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ Γ' Δ (((B ⇒ C) ^ β) ∷ Δ')
  → Maybe (cutConstraint m A α Γ ((B ^ β) ∷ Γ') Δ ((C ^ β) ∷ Δ'))
cutConstraint-down-right-ImpR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-ImpR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl (pf , mΓRem , p) =
    just
      (inr
        (∈Init-++⁺ˡ
          (pf ,
            mNew ,
            p)))
  where
    remInfo = pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = Γ'} mΓRem
    yInΓ' : pf ∈ Γ'
    yInΓ' = fst remInfo
    y≠A : Neg (pf ≡ (A ^ α))
    y≠A q = snd remInfo (sym q)
    mNew : pf ∈ (((B ^ β) ∷ Γ') -pf (A ^ α))
    mNew =
      pf-keep
        {x = (A ^ α)} {y = pf} {Γ = (B ^ β) ∷ Γ'}
        (there yInΓ')
        y≠A
... | inr (pf , mTail , p) with mTail
...   | here pf≡imp =
    just
      (inr
        (∈Init-++⁺ʳ (((B ^ β) ∷ Γ') -pf (A ^ α))
          ((C ^ β) ,
            here refl ,
            subst (λ z → α ⊑ z) (cong PFormula.pos pf≡imp) p)))
...   | there mΔ' =
    just
      (inr
        (∈Init-++⁺ʳ (((B ^ β) ∷ Γ') -pf (A ^ α))
          (pf , there mΔ' , p)))
cutConstraint-down-right-ImpR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-ImpR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {C = C} {α = α} {β = β}
  (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl (pf , mΓRem , p) =
    just
      (inr
        (∈Init-++⁺ˡ
          (pf ,
            mNew ,
            p)))
  where
    remInfo = pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = Γ'} mΓRem
    yInΓ' : pf ∈ Γ'
    yInΓ' = fst remInfo
    y≠A : Neg (pf ≡ (A ^ α))
    y≠A q = snd remInfo (sym q)
    mNew : pf ∈ (((B ^ β) ∷ Γ') -pf (A ^ α))
    mNew =
      pf-keep
        {x = (A ^ α)} {y = pf} {Γ = (B ^ β) ∷ Γ'}
        (there yInΓ')
        y≠A
... | inr (pf , mTail , p) with mTail
...   | here pf≡imp =
    just
      (inr
        (∈Init-++⁺ʳ (((B ^ β) ∷ Γ') -pf (A ^ α))
          ((C ^ β) ,
            here refl ,
            subst (λ z → α ⊑ z) (cong PFormula.pos pf≡imp) p)))
...   | there mΔ' =
    just
      (inr
        (∈Init-++⁺ʳ (((B ^ β) ∷ Γ') -pf (A ^ α))
          (pf , there mΔ' , p)))
cutConstraint-down-right-ImpR-gen D c = just tt
cutConstraint-down-right-ImpR-gen T c = just tt
cutConstraint-down-right-ImpR-gen D4 c = just tt
cutConstraint-down-right-ImpR-gen S4 c = just tt
cutConstraint-down-right-ImpR-gen S4dot2 c = just tt
cutConstraint-down-right-ImpR-gen S5 c = just tt

cutConstraint-down-right-ImpR :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ Γ' Δ (((B ⇒ C) ^ β) ∷ Δ')
  → Maybe (cutConstraint M A α Γ ((B ^ β) ∷ Γ') Δ ((C ^ β) ∷ Δ'))
cutConstraint-down-right-ImpR = cutConstraint-down-right-ImpR-gen M

cutConstraint-down-right-NotR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → cutConstraint m A α Γ Γ' Δ ((Not B ^ β) ∷ Δ')
  → Maybe (cutConstraint m A α Γ ((B ^ β) ∷ Γ') Δ Δ')
cutConstraint-down-right-NotR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-NotR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl (pf , mΓRem , p) =
    just
      (inr
        (∈Init-++⁺ˡ
          (pf ,
            mNew ,
            p)))
  where
    remInfo = pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = Γ'} mΓRem
    yInΓ' : pf ∈ Γ'
    yInΓ' = fst remInfo
    y≠A : Neg (pf ≡ (A ^ α))
    y≠A q = snd remInfo (sym q)
    mNew : pf ∈ (((B ^ β) ∷ Γ') -pf (A ^ α))
    mNew =
      pf-keep
        {x = (A ^ α)} {y = pf} {Γ = (B ^ β) ∷ Γ'}
        (there yInΓ')
        y≠A
... | inr (pf , mTail , p) with mTail
...   | here pf≡notB =
      headCase ((B ^ β) ≟pf (A ^ α))
      where
        pαβ : α ⊑ β
        pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡notB) p

        headCase : Dec ((B ^ β) ≡ (A ^ α))
          → Maybe (cutConstraint K A α Γ ((B ^ β) ∷ Γ') Δ Δ')
        headCase (yes _) = nothing
        headCase (no b≢a) =
          just (inr (subst (α ∈Init_) eqCtx wHead))
          where
            eqRem : (((B ^ β) ∷ Γ') -pf (A ^ α))
                 ≡ ((B ^ β) ∷ (Γ' -pf (A ^ α)))
            eqRem =
              pf-cons-neq
                {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'}
                (λ q → b≢a (sym q))

            eqCtx : ((B ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ'
                ≡ (((B ^ β) ∷ Γ') -pf (A ^ α)) ++ Δ'
            eqCtx = cong (_++ Δ') (sym eqRem)

            wHead : α ∈Init (((B ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ')
            wHead =
              ∈Init-++⁺ˡ
                {Γ = (B ^ β) ∷ (Γ' -pf (A ^ α))}
                {Δ = Δ'}
                ((B ^ β) , here refl , pαβ)
...   | there mΔ' =
      just
        (inr
          (∈Init-++⁺ʳ (((B ^ β) ∷ Γ') -pf (A ^ α))
            (pf , mΔ' , p)))
cutConstraint-down-right-NotR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inl w) = just (inl w)
cutConstraint-down-right-NotR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β}
  (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl (pf , mΓRem , p) =
    just
      (inr
        (∈Init-++⁺ˡ
          (pf ,
            mNew ,
            p)))
  where
    remInfo = pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = Γ'} mΓRem
    yInΓ' : pf ∈ Γ'
    yInΓ' = fst remInfo
    y≠A : Neg (pf ≡ (A ^ α))
    y≠A q = snd remInfo (sym q)
    mNew : pf ∈ (((B ^ β) ∷ Γ') -pf (A ^ α))
    mNew =
      pf-keep
        {x = (A ^ α)} {y = pf} {Γ = (B ^ β) ∷ Γ'}
        (there yInΓ')
        y≠A
... | inr (pf , mTail , p) with mTail
...   | here pf≡notB =
      headCase ((B ^ β) ≟pf (A ^ α))
      where
        pαβ : α ⊑ β
        pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡notB) p

        headCase : Dec ((B ^ β) ≡ (A ^ α))
          → Maybe (cutConstraint K4 A α Γ ((B ^ β) ∷ Γ') Δ Δ')
        headCase (yes _) = nothing
        headCase (no b≢a) =
          just (inr (subst (α ∈Init_) eqCtx wHead))
          where
            eqRem : (((B ^ β) ∷ Γ') -pf (A ^ α))
                 ≡ ((B ^ β) ∷ (Γ' -pf (A ^ α)))
            eqRem =
              pf-cons-neq
                {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'}
                (λ q → b≢a (sym q))

            eqCtx : ((B ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ'
                ≡ (((B ^ β) ∷ Γ') -pf (A ^ α)) ++ Δ'
            eqCtx = cong (_++ Δ') (sym eqRem)

            wHead : α ∈Init (((B ^ β) ∷ (Γ' -pf (A ^ α))) ++ Δ')
            wHead =
              ∈Init-++⁺ˡ
                {Γ = (B ^ β) ∷ (Γ' -pf (A ^ α))}
                {Δ = Δ'}
                ((B ^ β) , here refl , pαβ)
...   | there mΔ' =
      just
        (inr
          (∈Init-++⁺ʳ (((B ^ β) ∷ Γ') -pf (A ^ α))
            (pf , mΔ' , p)))
cutConstraint-down-right-NotR-gen D c = just tt
cutConstraint-down-right-NotR-gen T c = just tt
cutConstraint-down-right-NotR-gen D4 c = just tt
cutConstraint-down-right-NotR-gen S4 c = just tt
cutConstraint-down-right-NotR-gen S4dot2 c = just tt
cutConstraint-down-right-NotR-gen S5 c = just tt

cutConstraint-down-right-NotR :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → cutConstraint M A α Γ Γ' Δ ((Not B ^ β) ∷ Δ')
  → Maybe (cutConstraint M A α Γ ((B ^ β) ∷ Γ') Δ Δ')
cutConstraint-down-right-NotR = cutConstraint-down-right-NotR-gen M

cutConstraint-down-right-BoxL-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → modalConstraint m β γ Γ' Δ'
  → cutConstraint m A α Γ (Γ' ++ [ □ B ^ β ]) Δ Δ'
  → Maybe (cutConstraint m A α Γ (Γ' ++ [ B ^ γ ]) Δ Δ')
cutConstraint-down-right-BoxL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inl w) = just (inl w)
cutConstraint-down-right-BoxL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inr w) with ∈Init-++⁻ (((Γ' ++ [ □ B ^ β ]) -pf (A ^ α))) w
... | inr wΔ' = just (inr (∈Init-++⁺ʳ (((Γ' ++ [ B ^ γ ]) -pf (A ^ α))) wΔ'))
... | inl (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = Γ' ++ [ □ B ^ β ]} mRem
...   | yInOrig , y≠A with ∈-++⁻ Γ' yInOrig
...     | inl yInΓ' =
      just
        (inr
          (∈Init-++⁺ˡ
            (pf ,
              pf-keep
                {x = (A ^ α)} {y = pf} {Γ = Γ' ++ [ B ^ γ ]}
                (∈-++⁺ˡ yInΓ') (λ q → y≠A (sym q)) ,
              p)))
...     | inr yInTail with yInTail
...       | here pf≡box =
          headCase ((B ^ γ) ≟pf (A ^ α))
          where
            pαβ : α ⊑ β
            pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡box) p

            pβγ : β ⊑ γ
            pβγ = modalConstraint-prefix-K {β = β} {γ = γ} {Γ = Γ'} {Δ = Δ'} mc

            pαγ : α ⊑ γ
            pαγ = ⊑-trans pαβ pβγ

            headCase : Dec ((B ^ γ) ≡ (A ^ α))
              → Maybe (cutConstraint K A α Γ (Γ' ++ [ B ^ γ ]) Δ Δ')
            headCase (yes _) = nothing
            headCase (no b≢a) =
              just
                (inr
                  (∈Init-++⁺ˡ
                    ((B ^ γ) ,
                      pf-keep
                        {x = (A ^ α)} {y = (B ^ γ)} {Γ = Γ' ++ [ B ^ γ ]}
                        (∈-++⁺ʳ Γ' (here refl))
                        (λ q → b≢a q) ,
                      pαγ)))
...       | there ()
cutConstraint-down-right-BoxL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inl w) = just (inl w)
cutConstraint-down-right-BoxL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inr w) with ∈Init-++⁻ (((Γ' ++ [ □ B ^ β ]) -pf (A ^ α))) w
... | inr wΔ' = just (inr (∈Init-++⁺ʳ (((Γ' ++ [ B ^ γ ]) -pf (A ^ α))) wΔ'))
... | inl (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = Γ' ++ [ □ B ^ β ]} mRem
...   | yInOrig , y≠A with ∈-++⁻ Γ' yInOrig
...     | inl yInΓ' =
      just
        (inr
          (∈Init-++⁺ˡ
            (pf ,
              pf-keep
                {x = (A ^ α)} {y = pf} {Γ = Γ' ++ [ B ^ γ ]}
                (∈-++⁺ˡ yInΓ') (λ q → y≠A (sym q)) ,
              p)))
...     | inr yInTail with yInTail
...       | here pf≡box =
          headCase ((B ^ γ) ≟pf (A ^ α))
          where
            pαβ : α ⊑ β
            pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡box) p

            pβγ : β ⊑ γ
            pβγ = modalConstraint-prefix-K4 {β = β} {γ = γ} {Γ = Γ'} {Δ = Δ'} mc

            pαγ : α ⊑ γ
            pαγ = ⊑-trans pαβ pβγ

            headCase : Dec ((B ^ γ) ≡ (A ^ α))
              → Maybe (cutConstraint K4 A α Γ (Γ' ++ [ B ^ γ ]) Δ Δ')
            headCase (yes _) = nothing
            headCase (no b≢a) =
              just
                (inr
                  (∈Init-++⁺ˡ
                    ((B ^ γ) ,
                      pf-keep
                        {x = (A ^ α)} {y = (B ^ γ)} {Γ = Γ' ++ [ B ^ γ ]}
                        (∈-++⁺ʳ Γ' (here refl))
                        (λ q → b≢a q) ,
                      pαγ)))
...       | there ()
cutConstraint-down-right-BoxL-gen D mc c = just tt
cutConstraint-down-right-BoxL-gen T mc c = just tt
cutConstraint-down-right-BoxL-gen D4 mc c = just tt
cutConstraint-down-right-BoxL-gen S4 mc c = just tt
cutConstraint-down-right-BoxL-gen S4dot2 mc c = just tt
cutConstraint-down-right-BoxL-gen S5 mc c = just tt

cutConstraint-down-right-BoxL :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → modalConstraint M β γ Γ' Δ'
  → cutConstraint M A α Γ (Γ' ++ [ □ B ^ β ]) Δ Δ'
  → Maybe (cutConstraint M A α Γ (Γ' ++ [ B ^ γ ]) Δ Δ')
cutConstraint-down-right-BoxL = cutConstraint-down-right-BoxL-gen M

cutConstraint-down-right-BoxR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position} {x : Token}
  → cutConstraint m A α Γ Γ' Δ ((□ B ^ β) ∷ Δ')
  → cutConstraint m A α Γ Γ' Δ ((B ^ (β ∘ [ x ])) ∷ Δ')
cutConstraint-down-right-BoxR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inl w) = inl w
cutConstraint-down-right-BoxR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl wΓ = inr (∈Init-++⁺ˡ wΓ)
... | inr (pf , mTail , p) with mTail
...   | here pf≡box =
    inr
      (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
        ((B ^ (β ∘ [ x ])) ,
          here refl ,
          pαβx))
    where
      pαβ : α ⊑ β
      pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡box) p

      pαβx : α ⊑ (β ∘ [ x ])
      pαβx = ⊑-trans pαβ (prefix-step-right β x)
...   | there mΔ' = inr (∈Init-++⁺ʳ (Γ' -pf (A ^ α)) (pf , there mΔ' , p))
cutConstraint-down-right-BoxR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inl w) = inl w
cutConstraint-down-right-BoxR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl wΓ = inr (∈Init-++⁺ˡ wΓ)
... | inr (pf , mTail , p) with mTail
...   | here pf≡box =
    inr
      (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
        ((B ^ (β ∘ [ x ])) ,
          here refl ,
          pαβx))
    where
      pαβ : α ⊑ β
      pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡box) p

      pαβx : α ⊑ (β ∘ [ x ])
      pαβx = ⊑-trans pαβ (prefix-step-right β x)
...   | there mΔ' = inr (∈Init-++⁺ʳ (Γ' -pf (A ^ α)) (pf , there mΔ' , p))
cutConstraint-down-right-BoxR-gen D c = tt
cutConstraint-down-right-BoxR-gen T c = tt
cutConstraint-down-right-BoxR-gen D4 c = tt
cutConstraint-down-right-BoxR-gen S4 c = tt
cutConstraint-down-right-BoxR-gen S4dot2 c = tt
cutConstraint-down-right-BoxR-gen S5 c = tt

cutConstraint-down-right-BoxR :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position} {x : Token}
  → cutConstraint M A α Γ Γ' Δ ((□ B ^ β) ∷ Δ')
  → cutConstraint M A α Γ Γ' Δ ((B ^ (β ∘ [ x ])) ∷ Δ')
cutConstraint-down-right-BoxR = cutConstraint-down-right-BoxR-gen M

cutConstraint-down-right-DiaL-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position} {x : Token}
  → cutConstraint m A α Γ (Γ' ++ [ ♢ B ^ β ]) Δ Δ'
  → Maybe (cutConstraint m A α Γ (Γ' ++ [ B ^ (β ∘ [ x ]) ]) Δ Δ')
cutConstraint-down-right-DiaL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inl w) = just (inl w)
cutConstraint-down-right-DiaL-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inr w) with ∈Init-++⁻ (((Γ' ++ [ ♢ B ^ β ]) -pf (A ^ α))) w
... | inr wΔ' = just (inr (∈Init-++⁺ʳ (((Γ' ++ [ B ^ (β ∘ [ x ]) ]) -pf (A ^ α))) wΔ'))
... | inl (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = Γ' ++ [ ♢ B ^ β ]} mRem
...   | yInOrig , y≠A with ∈-++⁻ Γ' yInOrig
...     | inl yInΓ' =
      just
        (inr
          (∈Init-++⁺ˡ
            (pf ,
              pf-keep
                {x = (A ^ α)} {y = pf} {Γ = Γ' ++ [ B ^ (β ∘ [ x ]) ]}
                (∈-++⁺ˡ yInΓ') (λ q → y≠A (sym q)) ,
              p)))
...     | inr yInTail with yInTail
...       | here pf≡dia =
          headCase ((B ^ (β ∘ [ x ])) ≟pf (A ^ α))
          where
            pαβ : α ⊑ β
            pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡dia) p

            pαβx : α ⊑ (β ∘ [ x ])
            pαβx = ⊑-trans pαβ (prefix-step-right β x)

            headCase : Dec ((B ^ (β ∘ [ x ])) ≡ (A ^ α))
              → Maybe (cutConstraint K A α Γ (Γ' ++ [ B ^ (β ∘ [ x ]) ]) Δ Δ')
            headCase (yes _) = nothing
            headCase (no b≢a) =
              just
                (inr
                  (∈Init-++⁺ˡ
                    ((B ^ (β ∘ [ x ])) ,
                      pf-keep
                        {x = (A ^ α)} {y = (B ^ (β ∘ [ x ]))} {Γ = Γ' ++ [ B ^ (β ∘ [ x ]) ]}
                        (∈-++⁺ʳ Γ' (here refl))
                        (λ q → b≢a q) ,
                      pαβx)))
...       | there ()
cutConstraint-down-right-DiaL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inl w) = just (inl w)
cutConstraint-down-right-DiaL-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {x = x}
  (inr w) with ∈Init-++⁻ (((Γ' ++ [ ♢ B ^ β ]) -pf (A ^ α))) w
... | inr wΔ' = just (inr (∈Init-++⁺ʳ (((Γ' ++ [ B ^ (β ∘ [ x ]) ]) -pf (A ^ α))) wΔ'))
... | inl (pf , mRem , p) with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = Γ' ++ [ ♢ B ^ β ]} mRem
...   | yInOrig , y≠A with ∈-++⁻ Γ' yInOrig
...     | inl yInΓ' =
      just
        (inr
          (∈Init-++⁺ˡ
            (pf ,
              pf-keep
                {x = (A ^ α)} {y = pf} {Γ = Γ' ++ [ B ^ (β ∘ [ x ]) ]}
                (∈-++⁺ˡ yInΓ') (λ q → y≠A (sym q)) ,
              p)))
...     | inr yInTail with yInTail
...       | here pf≡dia =
          headCase ((B ^ (β ∘ [ x ])) ≟pf (A ^ α))
          where
            pαβ : α ⊑ β
            pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡dia) p

            pαβx : α ⊑ (β ∘ [ x ])
            pαβx = ⊑-trans pαβ (prefix-step-right β x)

            headCase : Dec ((B ^ (β ∘ [ x ])) ≡ (A ^ α))
              → Maybe (cutConstraint K4 A α Γ (Γ' ++ [ B ^ (β ∘ [ x ]) ]) Δ Δ')
            headCase (yes _) = nothing
            headCase (no b≢a) =
              just
                (inr
                  (∈Init-++⁺ˡ
                    ((B ^ (β ∘ [ x ])) ,
                      pf-keep
                        {x = (A ^ α)} {y = (B ^ (β ∘ [ x ]))} {Γ = Γ' ++ [ B ^ (β ∘ [ x ]) ]}
                        (∈-++⁺ʳ Γ' (here refl))
                        (λ q → b≢a q) ,
                      pαβx)))
...       | there ()
cutConstraint-down-right-DiaL-gen D c = just tt
cutConstraint-down-right-DiaL-gen T c = just tt
cutConstraint-down-right-DiaL-gen D4 c = just tt
cutConstraint-down-right-DiaL-gen S4 c = just tt
cutConstraint-down-right-DiaL-gen S4dot2 c = just tt
cutConstraint-down-right-DiaL-gen S5 c = just tt

cutConstraint-down-right-DiaL :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position} {x : Token}
  → cutConstraint M A α Γ (Γ' ++ [ ♢ B ^ β ]) Δ Δ'
  → Maybe (cutConstraint M A α Γ (Γ' ++ [ B ^ (β ∘ [ x ]) ]) Δ Δ')
cutConstraint-down-right-DiaL = cutConstraint-down-right-DiaL-gen M

cutConstraint-down-right-DiaR-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → modalConstraint m β γ Γ' Δ'
  → cutConstraint m A α Γ Γ' Δ ((♢ B ^ β) ∷ Δ')
  → cutConstraint m A α Γ Γ' Δ ((B ^ γ) ∷ Δ')
cutConstraint-down-right-DiaR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inl w) = inl w
cutConstraint-down-right-DiaR-gen K
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl wΓ = inr (∈Init-++⁺ˡ wΓ)
... | inr (pf , mTail , p) with mTail
...   | here pf≡dia =
    inr
      (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
        ((B ^ γ) ,
          here refl ,
          pαγ))
    where
      pαβ : α ⊑ β
      pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡dia) p

      pβγ : β ⊑ γ
      pβγ = modalConstraint-prefix-K {β = β} {γ = γ} {Γ = Γ'} {Δ = Δ'} mc

      pαγ : α ⊑ γ
      pαγ = ⊑-trans pαβ pβγ
...   | there mΔ' = inr (∈Init-++⁺ʳ (Γ' -pf (A ^ α)) (pf , there mΔ' , p))
cutConstraint-down-right-DiaR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inl w) = inl w
cutConstraint-down-right-DiaR-gen K4
  {Γ} {Δ} {Γ'} {Δ'} {A = A} {B = B} {α = α} {β = β} {γ = γ}
  mc (inr w) with ∈Init-++⁻ (Γ' -pf (A ^ α)) w
... | inl wΓ = inr (∈Init-++⁺ˡ wΓ)
... | inr (pf , mTail , p) with mTail
...   | here pf≡dia =
    inr
      (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
        ((B ^ γ) ,
          here refl ,
          pαγ))
    where
      pαβ : α ⊑ β
      pαβ = subst (λ z → α ⊑ z) (cong PFormula.pos pf≡dia) p

      pβγ : β ⊑ γ
      pβγ = modalConstraint-prefix-K4 {β = β} {γ = γ} {Γ = Γ'} {Δ = Δ'} mc

      pαγ : α ⊑ γ
      pαγ = ⊑-trans pαβ pβγ
...   | there mΔ' = inr (∈Init-++⁺ʳ (Γ' -pf (A ^ α)) (pf , there mΔ' , p))
cutConstraint-down-right-DiaR-gen D mc c = tt
cutConstraint-down-right-DiaR-gen T mc c = tt
cutConstraint-down-right-DiaR-gen D4 mc c = tt
cutConstraint-down-right-DiaR-gen S4 mc c = tt
cutConstraint-down-right-DiaR-gen S4dot2 mc c = tt
cutConstraint-down-right-DiaR-gen S5 mc c = tt

cutConstraint-down-right-DiaR :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → modalConstraint M β γ Γ' Δ'
  → cutConstraint M A α Γ Γ' Δ ((♢ B ^ β) ∷ Δ')
  → cutConstraint M A α Γ Γ' Δ ((B ^ γ) ∷ Δ')
cutConstraint-down-right-DiaR = cutConstraint-down-right-DiaR-gen M

cutConstraint-up-right-ContractR :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → cutConstraint M A α Γ Γ' Δ ((C ^ γ) ∷ Δ')
  → cutConstraint M A α Γ Γ' Δ ((C ^ γ) ∷ (C ^ γ) ∷ Δ')
cutConstraint-up-right-ContractR {C = C} {γ = γ} c =
  cutConstraint-up-right-WeakenR {C = C} {γ = γ} c

cutConstraint-down-left-ExchangeL-gen :
  (m : Logic)
  → ∀ {Γ₁ Γ₂ Γ' Δ Δ'} {A : Formula} {α : Position} {c d : PFormula}
  → cutConstraint m A α (Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂) Γ' Δ Δ'
  → cutConstraint m A α (Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂) Γ' Δ Δ'
cutConstraint-down-left-ExchangeL-gen K
  {Γ₁} {Γ₂} {Γ'} {Δ} {Δ'} {A} {α} {c} {d} (inl w) =
  inl (∈Init-subset sub w)
  where
    Γswap = Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂
    Γorig = Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂

    sub : (Γswap ++ (Δ -pf (A ^ α))) ⊆ (Γorig ++ (Δ -pf (A ^ α)))
    sub = solveCtx⊆!
cutConstraint-down-left-ExchangeL-gen K
  {Γ₁} {Γ₂} {Γ'} {Δ} {Δ'} {A} {α} {c} {d} (inr w) =
  inr w
cutConstraint-down-left-ExchangeL-gen K4
  {Γ₁} {Γ₂} {Γ'} {Δ} {Δ'} {A} {α} {c} {d} (inl w) =
  inl (∈Init-subset sub w)
  where
    Γswap = Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂
    Γorig = Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂

    sub : (Γswap ++ (Δ -pf (A ^ α))) ⊆ (Γorig ++ (Δ -pf (A ^ α)))
    sub = solveCtx⊆!
cutConstraint-down-left-ExchangeL-gen K4
  {Γ₁} {Γ₂} {Γ'} {Δ} {Δ'} {A} {α} {c} {d} (inr w) =
  inr w
cutConstraint-down-left-ExchangeL-gen D c = tt
cutConstraint-down-left-ExchangeL-gen T c = tt
cutConstraint-down-left-ExchangeL-gen D4 c = tt
cutConstraint-down-left-ExchangeL-gen S4 c = tt
cutConstraint-down-left-ExchangeL-gen S4dot2 c = tt
cutConstraint-down-left-ExchangeL-gen S5 c = tt

cutConstraint-down-left-ExchangeL :
  ∀ {Γ₁ Γ₂ Γ' Δ Δ'} {A : Formula} {α : Position} {c d : PFormula}
  → cutConstraint M A α (Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂) Γ' Δ Δ'
  → cutConstraint M A α (Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂) Γ' Δ Δ'
cutConstraint-down-left-ExchangeL = cutConstraint-down-left-ExchangeL-gen M

cutConstraint-down-right-ExchangeR-gen :
  (m : Logic)
  → ∀ {Γ Γ' Δ Δ₁ Δ₂} {A : Formula} {α : Position} {c d : PFormula}
  → cutConstraint m A α Γ Γ' Δ (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂)
  → cutConstraint m A α Γ Γ' Δ (Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂)
cutConstraint-down-right-ExchangeR-gen K
  {Γ} {Γ'} {Δ} {Δ₁} {Δ₂} {A} {α} {c} {d} (inl w) =
  inl w
cutConstraint-down-right-ExchangeR-gen K
  {Γ} {Γ'} {Δ} {Δ₁} {Δ₂} {A} {α} {c} {d} (inr w) =
  inr (∈Init-subset sub w)
  where
    sub : ((Γ' -pf (A ^ α)) ++ (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂))
       ⊆ (((Γ' -pf (A ^ α)) ++ (Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂)))
    sub = solveCtx⊆!
cutConstraint-down-right-ExchangeR-gen K4
  {Γ} {Γ'} {Δ} {Δ₁} {Δ₂} {A} {α} {c} {d} (inl w) =
  inl w
cutConstraint-down-right-ExchangeR-gen K4
  {Γ} {Γ'} {Δ} {Δ₁} {Δ₂} {A} {α} {c} {d} (inr w) =
  inr (∈Init-subset sub w)
  where
    sub : ((Γ' -pf (A ^ α)) ++ (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂))
       ⊆ (((Γ' -pf (A ^ α)) ++ (Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂)))
    sub = solveCtx⊆!
cutConstraint-down-right-ExchangeR-gen D c = tt
cutConstraint-down-right-ExchangeR-gen T c = tt
cutConstraint-down-right-ExchangeR-gen D4 c = tt
cutConstraint-down-right-ExchangeR-gen S4 c = tt
cutConstraint-down-right-ExchangeR-gen S4dot2 c = tt
cutConstraint-down-right-ExchangeR-gen S5 c = tt

cutConstraint-down-right-ExchangeR :
  ∀ {Γ Γ' Δ Δ₁ Δ₂} {A : Formula} {α : Position} {c d : PFormula}
  → cutConstraint M A α Γ Γ' Δ (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂)
  → cutConstraint M A α Γ Γ' Δ (Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂)
cutConstraint-down-right-ExchangeR = cutConstraint-down-right-ExchangeR-gen M

cutConstraint-down-left-ExchangeR-gen :
  (m : Logic)
  → ∀ {Γ Γ' Δ' Δ₁ Δ₂} {A : Formula} {α : Position} {c d : PFormula}
  → cutConstraint m A α Γ Γ' (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂) Δ'
  → cutConstraint m A α Γ Γ' (Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂) Δ'
cutConstraint-down-left-ExchangeR-gen K
  {Γ} {Γ'} {Δ'} {Δ₁} {Δ₂} {A} {α} {c} {d} (inl w) =
  inl (∈Init-subset sub w)
  where
    Δswap = Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂
    Δorig = Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂

    sub : (Γ ++ (Δswap -pf (A ^ α))) ⊆ (Γ ++ (Δorig -pf (A ^ α)))
    sub = solveCtx⊆!
cutConstraint-down-left-ExchangeR-gen K
  {Γ} {Γ'} {Δ'} {Δ₁} {Δ₂} {A} {α} {c} {d} (inr w) =
  inr w
cutConstraint-down-left-ExchangeR-gen K4
  {Γ} {Γ'} {Δ'} {Δ₁} {Δ₂} {A} {α} {c} {d} (inl w) =
  inl (∈Init-subset sub w)
  where
    Δswap = Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂
    Δorig = Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂

    sub : (Γ ++ (Δswap -pf (A ^ α))) ⊆ (Γ ++ (Δorig -pf (A ^ α)))
    sub = solveCtx⊆!
cutConstraint-down-left-ExchangeR-gen K4
  {Γ} {Γ'} {Δ'} {Δ₁} {Δ₂} {A} {α} {c} {d} (inr w) =
  inr w
cutConstraint-down-left-ExchangeR-gen D c = tt
cutConstraint-down-left-ExchangeR-gen T c = tt
cutConstraint-down-left-ExchangeR-gen D4 c = tt
cutConstraint-down-left-ExchangeR-gen S4 c = tt
cutConstraint-down-left-ExchangeR-gen S4dot2 c = tt
cutConstraint-down-left-ExchangeR-gen S5 c = tt

cutConstraint-down-left-ExchangeR :
  ∀ {Γ Γ' Δ' Δ₁ Δ₂} {A : Formula} {α : Position} {c d : PFormula}
  → cutConstraint M A α Γ Γ' (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂) Δ'
  → cutConstraint M A α Γ Γ' (Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂) Δ'
cutConstraint-down-left-ExchangeR = cutConstraint-down-left-ExchangeR-gen M

cutConstraint-down-right-ExchangeL-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ₁ Γ₂ Δ'} {A : Formula} {α : Position} {c d : PFormula}
  → cutConstraint m A α Γ (Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂) Δ Δ'
  → cutConstraint m A α Γ (Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂) Δ Δ'
cutConstraint-down-right-ExchangeL-gen K
  {Γ} {Δ} {Γ₁} {Γ₂} {Δ'} {A} {α} {c} {d} (inl w) =
  inl w
cutConstraint-down-right-ExchangeL-gen K
  {Γ} {Δ} {Γ₁} {Γ₂} {Δ'} {A} {α} {c} {d} (inr w) =
  inr (∈Init-subset sub w)
  where
    Γswap = Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂
    Γorig = Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂

    sub : ((Γswap -pf (A ^ α)) ++ Δ') ⊆ ((Γorig -pf (A ^ α)) ++ Δ')
    sub = solveCtx⊆!
cutConstraint-down-right-ExchangeL-gen K4
  {Γ} {Δ} {Γ₁} {Γ₂} {Δ'} {A} {α} {c} {d} (inl w) =
  inl w
cutConstraint-down-right-ExchangeL-gen K4
  {Γ} {Δ} {Γ₁} {Γ₂} {Δ'} {A} {α} {c} {d} (inr w) =
  inr (∈Init-subset sub w)
  where
    Γswap = Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂
    Γorig = Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂

    sub : ((Γswap -pf (A ^ α)) ++ Δ') ⊆ ((Γorig -pf (A ^ α)) ++ Δ')
    sub = solveCtx⊆!
cutConstraint-down-right-ExchangeL-gen D c = tt
cutConstraint-down-right-ExchangeL-gen T c = tt
cutConstraint-down-right-ExchangeL-gen D4 c = tt
cutConstraint-down-right-ExchangeL-gen S4 c = tt
cutConstraint-down-right-ExchangeL-gen S4dot2 c = tt
cutConstraint-down-right-ExchangeL-gen S5 c = tt

cutConstraint-down-right-ExchangeL :
  ∀ {Γ Δ Γ₁ Γ₂ Δ'} {A : Formula} {α : Position} {c d : PFormula}
  → cutConstraint M A α Γ (Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂) Δ Δ'
  → cutConstraint M A α Γ (Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂) Δ Δ'
cutConstraint-down-right-ExchangeL = cutConstraint-down-right-ExchangeL-gen M

mix-lift-left-WeakenL :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((((C ^ γ) ∷ Γ) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-ContractL :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → (n : ℕ)
  → Σ ((((C ^ γ) ∷ (C ^ γ) ∷ Γ) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((((C ^ γ) ∷ Γ) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-ContractR :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((C ^ γ) ∷ (C ^ γ) ∷ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((C ^ γ) ∷ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-NotL :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((B ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((((Not B ^ β) ∷ Γ) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-NotR :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → Neg ((Not B ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((((B ^ β) ∷ Γ) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((Not B ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-AndL1 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → (n : ℕ)
  → Σ ((((B ^ β) ∷ Γ) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((((And B C ^ β) ∷ Γ) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-AndL2 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → (n : ℕ)
  → Σ ((((C ^ β) ∷ Γ) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((((And B C ^ β) ∷ Γ) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-OrR1 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → Neg ((Or B C ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((B ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((Or B C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-OrR2 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → Neg ((Or B C ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((Or B C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-ImpR :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → Neg (((B ⇒ C) ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((((B ^ β) ∷ Γ) ++ (Γ' -pf (A ^ α)))
      ⊢ ((((C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((B ⇒ C) ^ β) ∷ Δ) -pf (A ^ α) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-OrL :
  ∀ {Γ₁ Γ₂ Δ₁ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → Neg ((Or B C ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((((B ^ β) ∷ Γ₁) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ₁ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((((C ^ β) ∷ Γ₂) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ₂ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((((Or B C ^ β) ∷ (Γ₁ ++ Γ₂)) ++ (Γ' -pf (A ^ α)))
      ⊢ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-ImpL :
  ∀ {Γ₁ Γ₂ Δ₁ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → Neg (((B ⇒ C) ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((Γ₁ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((B ^ β) ∷ Δ₁) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((((C ^ β) ∷ Γ₂) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ₂ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ (((((B ⇒ C) ^ β) ∷ (Γ₁ ++ Γ₂)) ++ (Γ' -pf (A ^ α)))
      ⊢ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-Cut :
  ∀ {Γ₁ Γ₂ Δ₁ Δ₂ Γ' Δ'} {A A' : Formula} {α α' : Position}
  → cutConstraint M A' α'
      (Γ₁ ++ (Γ' -pf (A ^ α)))
      (Γ₂ ++ (Γ' -pf (A ^ α)))
      ((Δ₁ -pf (A ^ α)) ++ Δ')
      ((Δ₂ -pf (A ^ α)) ++ Δ')
  → (n : ℕ)
  → suc (degree A') ≤ n
  → Σ ((Γ₁ ++ (Γ' -pf (A ^ α)))
      ⊢ ((([ (A' ^ α') ] ++ Δ₁) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ (((Γ₂ ++ [ (A' ^ α') ]) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ₂ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ (((Γ₁ ++ Γ₂) ++ (Γ' -pf (A ^ α)))
      ⊢ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-BoxL :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → Neg ((□ B ^ β) ≡ (A ^ α))
  → modalConstraint M β γ (Γ ++ (Γ' -pf (A ^ α))) ((Δ -pf (A ^ α)) ++ Δ')
  → (n : ℕ)
  → Σ (((Γ ++ [ (B ^ γ) ]) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ (((Γ ++ [ (□ B ^ β) ]) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-DiaR :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → Neg ((♢ B ^ β) ≡ (A ^ α))
  → modalConstraint M β γ (Γ ++ (Γ' -pf (A ^ α))) ((Δ -pf (A ^ α)) ++ Δ')
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((([ (B ^ γ) ] ++ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((([ (♢ B ^ β) ] ++ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-AndR :
  ∀ {Γ₁ Γ₂ Δ₁ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → Neg ((And B C ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((Γ₁ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((B ^ β) ∷ Δ₁) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ₂ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((C ^ β) ∷ Δ₂) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ (((Γ₁ ++ Γ₂) ++ (Γ' -pf (A ^ α)))
      ⊢ ((((And B C ^ β) ∷ (Δ₁ ++ Δ₂)) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-NotL :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → Neg ((Not B ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ ((B ^ β) ∷ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (((Not B ^ β) ∷ Γ') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-AndL1 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → Neg ((And B C ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((Γ ++ (((B ^ β) ∷ Γ') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (((And B C ^ β) ∷ Γ') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-AndL2 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → Neg ((And B C ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((Γ ++ (((C ^ β) ∷ Γ') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (((And B C ^ β) ∷ Γ') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-OrR1 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ ((B ^ β) ∷ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ ((Or B C ^ β) ∷ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-OrR2 :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ ((C ^ β) ∷ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ ((Or B C ^ β) ∷ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-ImpR :
  ∀ {Γ Δ Γ' Δ'} {A B C : Formula} {α β : Position}
  → Neg (((B ⇒ C) ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((Γ ++ (((B ^ β) ∷ Γ') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ ((C ^ β) ∷ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ (((B ⇒ C) ^ β) ∷ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-NotR :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β : Position}
  → Neg ((Not B ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((Γ ++ (((B ^ β) ∷ Γ') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ ((Not B ^ β) ∷ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-WeakenR :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ ((C ^ γ) ∷ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-WeakenR :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((C ^ γ) ∷ Δ) -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-WeakenL :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (((C ^ γ) ∷ Γ') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-ContractL :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → (n : ℕ)
  → Σ ((Γ ++ (((C ^ γ) ∷ (C ^ γ) ∷ Γ') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (((C ^ γ) ∷ Γ') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-ContractR :
  ∀ {Γ Δ Γ' Δ'} {A C : Formula} {α γ : Position}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ ((C ^ γ) ∷ (C ^ γ) ∷ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ ((C ^ γ) ∷ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-ExchangeL :
  ∀ {Γ₁ Γ₂ Δ Γ' Δ'} {A : Formula} {α : Position} {c d : PFormula}
  → (n : ℕ)
  → Σ ((((Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      ) (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((((Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂) ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      ) (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-ExchangeR :
  ∀ {Γ Δ₁ Δ₂ Γ' Δ} {A : Formula} {α : Position} {c d : PFormula}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ (((Δ -pf (A ^ α)) ++ (Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂))))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ (((Δ -pf (A ^ α)) ++ (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂))))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-left-ExchangeR :
  ∀ {Γ Δ₁ Δ₂ Γ' Δ'} {A : Formula} {α : Position} {c d : PFormula}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂) -pf (A ^ α)) ++ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((((Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂) -pf (A ^ α)) ++ Δ')))
      (λ Π₀ → δ Π₀ ≤ n)

mix-lift-right-ExchangeL :
  ∀ {Γ Δ Γ₁ Γ₂ Δ'} {A : Formula} {α : Position} {c d : PFormula}
  → (n : ℕ)
  → Σ ((Γ ++ ((Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂) -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ ((Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂) -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)

cutConstraint-down-left-AndR₁-gen :
  (m : Logic)
  → ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α (Γ₁ ++ Γ₂) Γ' ((And B C ^ β) ∷ (Δ₁ ++ Δ₂)) Δ'
  → Maybe (cutConstraint m A α Γ₁ Γ' ((B ^ β) ∷ Δ₁) Δ')
cutConstraint-down-left-AndR₁-gen K c = nothing
cutConstraint-down-left-AndR₁-gen K4 c = nothing
cutConstraint-down-left-AndR₁-gen D c = just tt
cutConstraint-down-left-AndR₁-gen T c = just tt
cutConstraint-down-left-AndR₁-gen D4 c = just tt
cutConstraint-down-left-AndR₁-gen S4 c = just tt
cutConstraint-down-left-AndR₁-gen S4dot2 c = just tt
cutConstraint-down-left-AndR₁-gen S5 c = just tt

cutConstraint-down-left-AndR₁ :
  ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α (Γ₁ ++ Γ₂) Γ' ((And B C ^ β) ∷ (Δ₁ ++ Δ₂)) Δ'
  → Maybe (cutConstraint M A α Γ₁ Γ' ((B ^ β) ∷ Δ₁) Δ')
cutConstraint-down-left-AndR₁ = cutConstraint-down-left-AndR₁-gen M

cutConstraint-down-left-AndR₂-gen :
  (m : Logic)
  → ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α (Γ₁ ++ Γ₂) Γ' ((And B C ^ β) ∷ (Δ₁ ++ Δ₂)) Δ'
  → Maybe (cutConstraint m A α Γ₂ Γ' ((C ^ β) ∷ Δ₂) Δ')
cutConstraint-down-left-AndR₂-gen K c = nothing
cutConstraint-down-left-AndR₂-gen K4 c = nothing
cutConstraint-down-left-AndR₂-gen D c = just tt
cutConstraint-down-left-AndR₂-gen T c = just tt
cutConstraint-down-left-AndR₂-gen D4 c = just tt
cutConstraint-down-left-AndR₂-gen S4 c = just tt
cutConstraint-down-left-AndR₂-gen S4dot2 c = just tt
cutConstraint-down-left-AndR₂-gen S5 c = just tt

cutConstraint-down-left-AndR₂ :
  ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α (Γ₁ ++ Γ₂) Γ' ((And B C ^ β) ∷ (Δ₁ ++ Δ₂)) Δ'
  → Maybe (cutConstraint M A α Γ₂ Γ' ((C ^ β) ∷ Δ₂) Δ')
cutConstraint-down-left-AndR₂ = cutConstraint-down-left-AndR₂-gen M

cutConstraint-down-left-OrL₁-gen :
  (m : Logic)
  → ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α ((Or B C ^ β) ∷ (Γ₁ ++ Γ₂)) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint m A α ((B ^ β) ∷ Γ₁) Γ' Δ₁ Δ')
cutConstraint-down-left-OrL₁-gen K c = nothing
cutConstraint-down-left-OrL₁-gen K4 c = nothing
cutConstraint-down-left-OrL₁-gen D c = just tt
cutConstraint-down-left-OrL₁-gen T c = just tt
cutConstraint-down-left-OrL₁-gen D4 c = just tt
cutConstraint-down-left-OrL₁-gen S4 c = just tt
cutConstraint-down-left-OrL₁-gen S4dot2 c = just tt
cutConstraint-down-left-OrL₁-gen S5 c = just tt

cutConstraint-down-left-OrL₁ :
  ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α ((Or B C ^ β) ∷ (Γ₁ ++ Γ₂)) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint M A α ((B ^ β) ∷ Γ₁) Γ' Δ₁ Δ')
cutConstraint-down-left-OrL₁ = cutConstraint-down-left-OrL₁-gen M

cutConstraint-down-left-OrL₂-gen :
  (m : Logic)
  → ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α ((Or B C ^ β) ∷ (Γ₁ ++ Γ₂)) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint m A α ((C ^ β) ∷ Γ₂) Γ' Δ₂ Δ')
cutConstraint-down-left-OrL₂-gen K c = nothing
cutConstraint-down-left-OrL₂-gen K4 c = nothing
cutConstraint-down-left-OrL₂-gen D c = just tt
cutConstraint-down-left-OrL₂-gen T c = just tt
cutConstraint-down-left-OrL₂-gen D4 c = just tt
cutConstraint-down-left-OrL₂-gen S4 c = just tt
cutConstraint-down-left-OrL₂-gen S4dot2 c = just tt
cutConstraint-down-left-OrL₂-gen S5 c = just tt

cutConstraint-down-left-OrL₂ :
  ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α ((Or B C ^ β) ∷ (Γ₁ ++ Γ₂)) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint M A α ((C ^ β) ∷ Γ₂) Γ' Δ₂ Δ')
cutConstraint-down-left-OrL₂ = cutConstraint-down-left-OrL₂-gen M

cutConstraint-down-left-ImpL₁-gen :
  (m : Logic)
  → ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α (((B ⇒ C) ^ β) ∷ (Γ₁ ++ Γ₂)) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint m A α Γ₁ Γ' ((B ^ β) ∷ Δ₁) Δ')
cutConstraint-down-left-ImpL₁-gen K c = nothing
cutConstraint-down-left-ImpL₁-gen K4 c = nothing
cutConstraint-down-left-ImpL₁-gen D c = just tt
cutConstraint-down-left-ImpL₁-gen T c = just tt
cutConstraint-down-left-ImpL₁-gen D4 c = just tt
cutConstraint-down-left-ImpL₁-gen S4 c = just tt
cutConstraint-down-left-ImpL₁-gen S4dot2 c = just tt
cutConstraint-down-left-ImpL₁-gen S5 c = just tt

cutConstraint-down-left-ImpL₁ :
  ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α (((B ⇒ C) ^ β) ∷ (Γ₁ ++ Γ₂)) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint M A α Γ₁ Γ' ((B ^ β) ∷ Δ₁) Δ')
cutConstraint-down-left-ImpL₁ = cutConstraint-down-left-ImpL₁-gen M

cutConstraint-down-left-ImpL₂-gen :
  (m : Logic)
  → ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α (((B ⇒ C) ^ β) ∷ (Γ₁ ++ Γ₂)) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint m A α ((C ^ β) ∷ Γ₂) Γ' Δ₂ Δ')
cutConstraint-down-left-ImpL₂-gen K c = nothing
cutConstraint-down-left-ImpL₂-gen K4 c = nothing
cutConstraint-down-left-ImpL₂-gen D c = just tt
cutConstraint-down-left-ImpL₂-gen T c = just tt
cutConstraint-down-left-ImpL₂-gen D4 c = just tt
cutConstraint-down-left-ImpL₂-gen S4 c = just tt
cutConstraint-down-left-ImpL₂-gen S4dot2 c = just tt
cutConstraint-down-left-ImpL₂-gen S5 c = just tt

cutConstraint-down-left-ImpL₂ :
  ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α (((B ⇒ C) ^ β) ∷ (Γ₁ ++ Γ₂)) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint M A α ((C ^ β) ∷ Γ₂) Γ' Δ₂ Δ')
cutConstraint-down-left-ImpL₂ = cutConstraint-down-left-ImpL₂-gen M

cutConstraint-down-left-Cut₁-gen :
  (m : Logic)
  → ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A A' : Formula} {α α' : Position}
  → cutConstraint m A α (Γ₁ ++ Γ₂) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint m A α Γ₁ Γ' ([ (A' ^ α') ] ++ Δ₁) Δ')
cutConstraint-down-left-Cut₁-gen K c = nothing
cutConstraint-down-left-Cut₁-gen K4 c = nothing
cutConstraint-down-left-Cut₁-gen D c = just tt
cutConstraint-down-left-Cut₁-gen T c = just tt
cutConstraint-down-left-Cut₁-gen D4 c = just tt
cutConstraint-down-left-Cut₁-gen S4 c = just tt
cutConstraint-down-left-Cut₁-gen S4dot2 c = just tt
cutConstraint-down-left-Cut₁-gen S5 c = just tt

cutConstraint-down-left-Cut₁ :
  ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A A' : Formula} {α α' : Position}
  → cutConstraint M A α (Γ₁ ++ Γ₂) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint M A α Γ₁ Γ' ([ (A' ^ α') ] ++ Δ₁) Δ')
cutConstraint-down-left-Cut₁ = cutConstraint-down-left-Cut₁-gen M

cutConstraint-down-left-Cut₂-gen :
  (m : Logic)
  → ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A A' : Formula} {α α' : Position}
  → cutConstraint m A α (Γ₁ ++ Γ₂) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint m A α (Γ₂ ++ [ (A' ^ α') ]) Γ' Δ₂ Δ')
cutConstraint-down-left-Cut₂-gen K c = nothing
cutConstraint-down-left-Cut₂-gen K4 c = nothing
cutConstraint-down-left-Cut₂-gen D c = just tt
cutConstraint-down-left-Cut₂-gen T c = just tt
cutConstraint-down-left-Cut₂-gen D4 c = just tt
cutConstraint-down-left-Cut₂-gen S4 c = just tt
cutConstraint-down-left-Cut₂-gen S4dot2 c = just tt
cutConstraint-down-left-Cut₂-gen S5 c = just tt

cutConstraint-down-left-Cut₂ :
  ∀ {Γ₁ Δ₁ Γ₂ Δ₂ Γ' Δ'} {A A' : Formula} {α α' : Position}
  → cutConstraint M A α (Γ₁ ++ Γ₂) Γ' (Δ₁ ++ Δ₂) Δ'
  → Maybe (cutConstraint M A α (Γ₂ ++ [ (A' ^ α') ]) Γ' Δ₂ Δ')
cutConstraint-down-left-Cut₂ = cutConstraint-down-left-Cut₂-gen M

cutConstraint-down-right-AndR₁-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ (Γ₁' ++ Γ₂') Δ ((And B C ^ β) ∷ (Δ₁' ++ Δ₂'))
  → Maybe (cutConstraint m A α Γ Γ₁' Δ ((B ^ β) ∷ Δ₁'))
cutConstraint-down-right-AndR₁-gen K c = nothing
cutConstraint-down-right-AndR₁-gen K4 c = nothing
cutConstraint-down-right-AndR₁-gen D c = just tt
cutConstraint-down-right-AndR₁-gen T c = just tt
cutConstraint-down-right-AndR₁-gen D4 c = just tt
cutConstraint-down-right-AndR₁-gen S4 c = just tt
cutConstraint-down-right-AndR₁-gen S4dot2 c = just tt
cutConstraint-down-right-AndR₁-gen S5 c = just tt

cutConstraint-down-right-AndR₁ :
  ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ (Γ₁' ++ Γ₂') Δ ((And B C ^ β) ∷ (Δ₁' ++ Δ₂'))
  → Maybe (cutConstraint M A α Γ Γ₁' Δ ((B ^ β) ∷ Δ₁'))
cutConstraint-down-right-AndR₁ = cutConstraint-down-right-AndR₁-gen M

cutConstraint-down-right-AndR₂-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ (Γ₁' ++ Γ₂') Δ ((And B C ^ β) ∷ (Δ₁' ++ Δ₂'))
  → Maybe (cutConstraint m A α Γ Γ₂' Δ ((C ^ β) ∷ Δ₂'))
cutConstraint-down-right-AndR₂-gen K c = nothing
cutConstraint-down-right-AndR₂-gen K4 c = nothing
cutConstraint-down-right-AndR₂-gen D c = just tt
cutConstraint-down-right-AndR₂-gen T c = just tt
cutConstraint-down-right-AndR₂-gen D4 c = just tt
cutConstraint-down-right-AndR₂-gen S4 c = just tt
cutConstraint-down-right-AndR₂-gen S4dot2 c = just tt
cutConstraint-down-right-AndR₂-gen S5 c = just tt

cutConstraint-down-right-AndR₂ :
  ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ (Γ₁' ++ Γ₂') Δ ((And B C ^ β) ∷ (Δ₁' ++ Δ₂'))
  → Maybe (cutConstraint M A α Γ Γ₂' Δ ((C ^ β) ∷ Δ₂'))
cutConstraint-down-right-AndR₂ = cutConstraint-down-right-AndR₂-gen M

cutConstraint-down-right-OrL₁-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ ((Or B C ^ β) ∷ (Γ₁' ++ Γ₂')) Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint m A α Γ ((B ^ β) ∷ Γ₁') Δ Δ₁')
cutConstraint-down-right-OrL₁-gen K c = nothing
cutConstraint-down-right-OrL₁-gen K4 c = nothing
cutConstraint-down-right-OrL₁-gen D c = just tt
cutConstraint-down-right-OrL₁-gen T c = just tt
cutConstraint-down-right-OrL₁-gen D4 c = just tt
cutConstraint-down-right-OrL₁-gen S4 c = just tt
cutConstraint-down-right-OrL₁-gen S4dot2 c = just tt
cutConstraint-down-right-OrL₁-gen S5 c = just tt

cutConstraint-down-right-OrL₁ :
  ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ ((Or B C ^ β) ∷ (Γ₁' ++ Γ₂')) Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint M A α Γ ((B ^ β) ∷ Γ₁') Δ Δ₁')
cutConstraint-down-right-OrL₁ = cutConstraint-down-right-OrL₁-gen M

cutConstraint-down-right-OrL₂-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ ((Or B C ^ β) ∷ (Γ₁' ++ Γ₂')) Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint m A α Γ ((C ^ β) ∷ Γ₂') Δ Δ₂')
cutConstraint-down-right-OrL₂-gen K c = nothing
cutConstraint-down-right-OrL₂-gen K4 c = nothing
cutConstraint-down-right-OrL₂-gen D c = just tt
cutConstraint-down-right-OrL₂-gen T c = just tt
cutConstraint-down-right-OrL₂-gen D4 c = just tt
cutConstraint-down-right-OrL₂-gen S4 c = just tt
cutConstraint-down-right-OrL₂-gen S4dot2 c = just tt
cutConstraint-down-right-OrL₂-gen S5 c = just tt

cutConstraint-down-right-OrL₂ :
  ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ ((Or B C ^ β) ∷ (Γ₁' ++ Γ₂')) Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint M A α Γ ((C ^ β) ∷ Γ₂') Δ Δ₂')
cutConstraint-down-right-OrL₂ = cutConstraint-down-right-OrL₂-gen M

cutConstraint-down-right-ImpL₁-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ (((B ⇒ C) ^ β) ∷ (Γ₁' ++ Γ₂')) Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint m A α Γ Γ₁' Δ ((B ^ β) ∷ Δ₁'))
cutConstraint-down-right-ImpL₁-gen K c = nothing
cutConstraint-down-right-ImpL₁-gen K4 c = nothing
cutConstraint-down-right-ImpL₁-gen D c = just tt
cutConstraint-down-right-ImpL₁-gen T c = just tt
cutConstraint-down-right-ImpL₁-gen D4 c = just tt
cutConstraint-down-right-ImpL₁-gen S4 c = just tt
cutConstraint-down-right-ImpL₁-gen S4dot2 c = just tt
cutConstraint-down-right-ImpL₁-gen S5 c = just tt

cutConstraint-down-right-ImpL₁ :
  ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ (((B ⇒ C) ^ β) ∷ (Γ₁' ++ Γ₂')) Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint M A α Γ Γ₁' Δ ((B ^ β) ∷ Δ₁'))
cutConstraint-down-right-ImpL₁ = cutConstraint-down-right-ImpL₁-gen M

cutConstraint-down-right-ImpL₂-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint m A α Γ (((B ⇒ C) ^ β) ∷ (Γ₁' ++ Γ₂')) Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint m A α Γ ((C ^ β) ∷ Γ₂') Δ Δ₂')
cutConstraint-down-right-ImpL₂-gen K c = nothing
cutConstraint-down-right-ImpL₂-gen K4 c = nothing
cutConstraint-down-right-ImpL₂-gen D c = just tt
cutConstraint-down-right-ImpL₂-gen T c = just tt
cutConstraint-down-right-ImpL₂-gen D4 c = just tt
cutConstraint-down-right-ImpL₂-gen S4 c = just tt
cutConstraint-down-right-ImpL₂-gen S4dot2 c = just tt
cutConstraint-down-right-ImpL₂-gen S5 c = just tt

cutConstraint-down-right-ImpL₂ :
  ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A B C : Formula} {α β : Position}
  → cutConstraint M A α Γ (((B ⇒ C) ^ β) ∷ (Γ₁' ++ Γ₂')) Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint M A α Γ ((C ^ β) ∷ Γ₂') Δ Δ₂')
cutConstraint-down-right-ImpL₂ = cutConstraint-down-right-ImpL₂-gen M

cutConstraint-down-right-Cut₁-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A A' : Formula} {α α' : Position}
  → cutConstraint m A α Γ (Γ₁' ++ Γ₂') Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint m A α Γ Γ₁' Δ ([ (A' ^ α') ] ++ Δ₁'))
cutConstraint-down-right-Cut₁-gen K c = nothing
cutConstraint-down-right-Cut₁-gen K4 c = nothing
cutConstraint-down-right-Cut₁-gen D c = just tt
cutConstraint-down-right-Cut₁-gen T c = just tt
cutConstraint-down-right-Cut₁-gen D4 c = just tt
cutConstraint-down-right-Cut₁-gen S4 c = just tt
cutConstraint-down-right-Cut₁-gen S4dot2 c = just tt
cutConstraint-down-right-Cut₁-gen S5 c = just tt

cutConstraint-down-right-Cut₁ :
  ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A A' : Formula} {α α' : Position}
  → cutConstraint M A α Γ (Γ₁' ++ Γ₂') Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint M A α Γ Γ₁' Δ ([ (A' ^ α') ] ++ Δ₁'))
cutConstraint-down-right-Cut₁ = cutConstraint-down-right-Cut₁-gen M

cutConstraint-down-right-Cut₂-gen :
  (m : Logic)
  → ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A A' : Formula} {α α' : Position}
  → cutConstraint m A α Γ (Γ₁' ++ Γ₂') Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint m A α Γ (Γ₂' ++ [ (A' ^ α') ]) Δ Δ₂')
cutConstraint-down-right-Cut₂-gen K c = nothing
cutConstraint-down-right-Cut₂-gen K4 c = nothing
cutConstraint-down-right-Cut₂-gen D c = just tt
cutConstraint-down-right-Cut₂-gen T c = just tt
cutConstraint-down-right-Cut₂-gen D4 c = just tt
cutConstraint-down-right-Cut₂-gen S4 c = just tt
cutConstraint-down-right-Cut₂-gen S4dot2 c = just tt
cutConstraint-down-right-Cut₂-gen S5 c = just tt

cutConstraint-down-right-Cut₂ :
  ∀ {Γ Δ Γ₁' Δ₁' Γ₂' Δ₂'} {A A' : Formula} {α α' : Position}
  → cutConstraint M A α Γ (Γ₁' ++ Γ₂') Δ (Δ₁' ++ Δ₂')
  → Maybe (cutConstraint M A α Γ (Γ₂' ++ [ (A' ^ α') ]) Δ Δ₂')
cutConstraint-down-right-Cut₂ = cutConstraint-down-right-Cut₂-gen M

cutConstraint-rebuild-gen :
  (m : Logic)
  → ∀ {A : Formula} {α : Position}
      {Γ₁ Γ₂ Δ₁ Δ₂ Γ₁' Γ₂' Δ₁' Δ₂' : Ctx}
  → cutConstraint m A α Γ₁ Γ₂ Δ₁ Δ₂
  → Maybe (cutConstraint m A α Γ₁' Γ₂' Δ₁' Δ₂')
cutConstraint-rebuild-gen K c = nothing
cutConstraint-rebuild-gen K4 c = nothing
cutConstraint-rebuild-gen D c = just tt
cutConstraint-rebuild-gen T c = just tt
cutConstraint-rebuild-gen D4 c = just tt
cutConstraint-rebuild-gen S4 c = just tt
cutConstraint-rebuild-gen S4dot2 c = just tt
cutConstraint-rebuild-gen S5 c = just tt

cutConstraint-rebuild :
  ∀ {A : Formula} {α : Position}
    {Γ₁ Γ₂ Δ₁ Δ₂ Γ₁' Γ₂' Δ₁' Δ₂' : Ctx}
  → cutConstraint M A α Γ₁ Γ₂ Δ₁ Δ₂
  → Maybe (cutConstraint M A α Γ₁' Γ₂' Δ₁' Δ₂')
cutConstraint-rebuild = cutConstraint-rebuild-gen M

modalConstraint-rebuild-gen :
  (m : Logic)
  → ∀ {α β : Position} {Γ Δ Γ' Δ' : Ctx}
  → modalConstraint m α β Γ Δ
  → Maybe (modalConstraint m α β Γ' Δ')
modalConstraint-rebuild-gen K (rel , _) = nothing
modalConstraint-rebuild-gen K4 (rel , _) = nothing
modalConstraint-rebuild-gen D mc = just mc
modalConstraint-rebuild-gen T mc = just mc
modalConstraint-rebuild-gen D4 mc = just mc
modalConstraint-rebuild-gen S4 mc = just mc
modalConstraint-rebuild-gen S4dot2 mc = just mc
modalConstraint-rebuild-gen S5 mc = just mc

modalConstraint-rebuild :
  ∀ {α β : Position} {Γ Δ Γ' Δ' : Ctx}
  → modalConstraint M α β Γ Δ
  → Maybe (modalConstraint M α β Γ' Δ')
modalConstraint-rebuild = modalConstraint-rebuild-gen M


------------------------------------------------------------------------
-- First non-principal branch combinators (left structural rules).

mix-lift-left-WeakenL n (Π₀ , dΠ₀≤n) =
  WeakenL Π₀ , dΠ₀≤n

mix-lift-left-ContractL {Γ} {Δ} {Γ'} {Δ'} {A} {C} {α} {γ} n (Π₀ , dΠ₀≤n) =
  Π₁ , dΠ₁≤n
  where
    subL : (((C ^ γ) ∷ (C ^ γ) ∷ Γ) ++ (Γ' -pf (A ^ α)))
         ⊆ (((C ^ γ) ∷ Γ) ++ (Γ' -pf (A ^ α)))
    subL = solveCtx⊆!

    Π₁ : (((C ^ γ) ∷ Γ) ++ (Γ' -pf (A ^ α)))
       ⊢ ((Δ -pf (A ^ α)) ++ Δ')
    Π₁ = structural subL subset-refl Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subL subset-refl Π₀ dΠ₀≤n)

mix-lift-left-ContractR {Γ} {Δ} {Γ'} {Δ'} {A} {C} {α} {γ} n (Π₀ , dΠ₀≤n) =
  Π₁ , dΠ₁≤n
  where
    subD : ((((C ^ γ) ∷ (C ^ γ) ∷ Δ) -pf (A ^ α)) ++ Δ')
        ⊆ ((((C ^ γ) ∷ Δ) -pf (A ^ α)) ++ Δ')
    subD = solveCtx⊆!

    Π₁ : (Γ ++ (Γ' -pf (A ^ α)))
       ⊢ ((((C ^ γ) ∷ Δ) -pf (A ^ α)) ++ Δ')
    Π₁ = structural subset-refl subD Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subset-refl subD Π₀ dΠ₀≤n)

mix-lift-left-NotL {Γ} {Δ} {Γ'} {Δ'} {A} {B} {α} {β} n (Π₀ , dΠ₀≤n) =
  liftCase ((B ^ β) ≟pf (A ^ α))
  where
    liftCase : Dec ((B ^ β) ≡ (A ^ α))
      → Σ ((((Not B ^ β) ∷ Γ) ++ (Γ' -pf (A ^ α)))
          ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
          (λ Π₀ → δ Π₀ ≤ n)

    liftCase (yes eqBA) =
      WeakenL Π₁ , dΠ₁≤n
      where
        eqD : ((((B ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
           ≡ ((Δ -pf (A ^ α)) ++ Δ')
        eqD = cong (_++ Δ') (pf-cons-eq {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ} eqBA)

        Π₁ : (Γ ++ (Γ' -pf (A ^ α)))
           ⊢ ((Δ -pf (A ^ α)) ++ Δ')
        Π₁ = subst (λ xs → (Γ ++ (Γ' -pf (A ^ α))) ⊢ xs) eqD Π₀

        dΠ₁≤n : δ Π₁ ≤ n
        dΠ₁≤n =
          snd (subst-δ-Δ eqD Π₀ dΠ₀≤n)

    liftCase (no b≢a) =
      NotL Π₁ , dΠ₁≤n
      where
        eqD : ((((B ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
           ≡ ((B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        eqD =
          cong (_++ Δ')
            (pf-cons-neq
              {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ}
              (λ p → b≢a (sym p)))

        Π₁ : (Γ ++ (Γ' -pf (A ^ α)))
           ⊢ ((B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Π₁ = subst (λ xs → (Γ ++ (Γ' -pf (A ^ α))) ⊢ xs) eqD Π₀

        dΠ₁≤n : δ Π₁ ≤ n
        dΠ₁≤n =
          snd (subst-δ-Δ eqD Π₀ dΠ₀≤n)

mix-lift-left-NotR {Γ} {Δ} {Γ'} {Δ'} {A} {B} {α} {β} notB≢A n (Π₀ , dΠ₀≤n) =
  Π₂ , dΠ₂≤n
  where
    Π₁ : (Γ ++ (Γ' -pf (A ^ α)))
       ⊢ ((Not B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    Π₁ = NotR Π₀

    eqD : ((((Not B ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
       ≡ ((Not B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    eqD =
      cong (_++ Δ')
        (pf-cons-neq
          {φ = (A ^ α)} {ψ = (Not B ^ β)} {Γ = Δ}
          (λ p → notB≢A (sym p)))

    Π₂ : (Γ ++ (Γ' -pf (A ^ α)))
       ⊢ ((((Not B ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
    Π₂ = subst (λ xs → (Γ ++ (Γ' -pf (A ^ α))) ⊢ xs) (sym eqD) Π₁

    dΠ₂≤n : δ Π₂ ≤ n
    dΠ₂≤n =
      snd (subst-δ-Δ (sym eqD) Π₁ dΠ₀≤n)

mix-lift-left-AndL1 n (Π₀ , dΠ₀≤n) =
  AndL1 Π₀ , dΠ₀≤n

mix-lift-left-AndL2 n (Π₀ , dΠ₀≤n) =
  AndL2 Π₀ , dΠ₀≤n

mix-lift-left-OrR1 {Γ} {Δ} {Γ'} {Δ'} {A} {B} {C} {α} {β} or≢a n (Π₀ , dΠ₀≤n) =
  orCase ((B ^ β) ≟pf (A ^ α))
  where
    lhs : Ctx
    lhs = Γ ++ (Γ' -pf (A ^ α))

    eqOrCons : (((Or B C ^ β) ∷ Δ) -pf (A ^ α))
            ≡ ((Or B C ^ β) ∷ (Δ -pf (A ^ α)))
    eqOrCons =
      pf-cons-neq
        {φ = (A ^ α)} {ψ = (Or B C ^ β)} {Γ = Δ}
        (λ q → or≢a (sym q))

    eqOr : ((((Or B C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
        ≡ ((Or B C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    eqOr = cong (_++ Δ') eqOrCons

    orCase : Dec ((B ^ β) ≡ (A ^ α))
      → Σ (lhs ⊢ ((((Or B C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ'))
          (λ Π₀ → δ Π₀ ≤ n)

    orCase (yes eqBA) =
      Πres , dΠres≤n
      where
        eqB : ((((B ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
           ≡ ((Δ -pf (A ^ α)) ++ Δ')
        eqB = cong (_++ Δ') (pf-cons-eq {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ} eqBA)

        Πbase : lhs ⊢ ((Δ -pf (A ^ α)) ++ Δ')
        Πbase = subst (λ xs → lhs ⊢ xs) eqB Π₀

        dΠbase≤n : δ Πbase ≤ n
        dΠbase≤n =
          snd (subst-δ-Δ eqB Π₀ dΠ₀≤n)

        Πweak : lhs ⊢ ((B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πweak = WeakenR Πbase

        Πor : lhs ⊢ ((Or B C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πor = OrR1 Πweak

        Πres : lhs ⊢ ((((Or B C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
        Πres = subst (λ xs → lhs ⊢ xs) (sym eqOr) Πor

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Δ (sym eqOr) Πor dΠbase≤n)

    orCase (no b≢a) =
      Πres , dΠres≤n
      where
        eqB : ((((B ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
           ≡ ((B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        eqB =
          cong (_++ Δ')
            (pf-cons-neq
              {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ}
              (λ q → b≢a (sym q)))

        Πprem : lhs ⊢ ((B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πprem = subst (λ xs → lhs ⊢ xs) eqB Π₀

        dΠprem≤n : δ Πprem ≤ n
        dΠprem≤n =
          snd (subst-δ-Δ eqB Π₀ dΠ₀≤n)

        Πor : lhs ⊢ ((Or B C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πor = OrR1 Πprem

        Πres : lhs ⊢ ((((Or B C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
        Πres = subst (λ xs → lhs ⊢ xs) (sym eqOr) Πor

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Δ (sym eqOr) Πor dΠprem≤n)

mix-lift-left-OrR2 {Γ} {Δ} {Γ'} {Δ'} {A} {B} {C} {α} {β} or≢a n (Π₀ , dΠ₀≤n) =
  orCase ((C ^ β) ≟pf (A ^ α))
  where
    lhs : Ctx
    lhs = Γ ++ (Γ' -pf (A ^ α))

    eqOrCons : (((Or B C ^ β) ∷ Δ) -pf (A ^ α))
            ≡ ((Or B C ^ β) ∷ (Δ -pf (A ^ α)))
    eqOrCons =
      pf-cons-neq
        {φ = (A ^ α)} {ψ = (Or B C ^ β)} {Γ = Δ}
        (λ q → or≢a (sym q))

    eqOr : ((((Or B C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
        ≡ ((Or B C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    eqOr = cong (_++ Δ') eqOrCons

    orCase : Dec ((C ^ β) ≡ (A ^ α))
      → Σ (lhs ⊢ ((((Or B C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ'))
          (λ Π₀ → δ Π₀ ≤ n)

    orCase (yes eqCA) =
      Πres , dΠres≤n
      where
        eqC : ((((C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
           ≡ ((Δ -pf (A ^ α)) ++ Δ')
        eqC = cong (_++ Δ') (pf-cons-eq {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Δ} eqCA)

        Πbase : lhs ⊢ ((Δ -pf (A ^ α)) ++ Δ')
        Πbase = subst (λ xs → lhs ⊢ xs) eqC Π₀

        dΠbase≤n : δ Πbase ≤ n
        dΠbase≤n =
          snd (subst-δ-Δ eqC Π₀ dΠ₀≤n)

        Πweak : lhs ⊢ ((C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πweak = WeakenR Πbase

        Πor : lhs ⊢ ((Or B C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πor = OrR2 Πweak

        Πres : lhs ⊢ ((((Or B C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
        Πres = subst (λ xs → lhs ⊢ xs) (sym eqOr) Πor

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Δ (sym eqOr) Πor dΠbase≤n)

    orCase (no c≢a) =
      Πres , dΠres≤n
      where
        eqC : ((((C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
           ≡ ((C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        eqC =
          cong (_++ Δ')
            (pf-cons-neq
              {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Δ}
              (λ q → c≢a (sym q)))

        Πprem : lhs ⊢ ((C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πprem = subst (λ xs → lhs ⊢ xs) eqC Π₀

        dΠprem≤n : δ Πprem ≤ n
        dΠprem≤n =
          snd (subst-δ-Δ eqC Π₀ dΠ₀≤n)

        Πor : lhs ⊢ ((Or B C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πor = OrR2 Πprem

        Πres : lhs ⊢ ((((Or B C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
        Πres = subst (λ xs → lhs ⊢ xs) (sym eqOr) Πor

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Δ (sym eqOr) Πor dΠprem≤n)

mix-lift-left-ImpR {Γ} {Δ} {Γ'} {Δ'} {A} {B} {C} {α} {β} imp≢a n (Π₀ , dΠ₀≤n) =
  impCase ((C ^ β) ≟pf (A ^ α))
  where
    lhs : Ctx
    lhs = Γ ++ (Γ' -pf (A ^ α))

    lhsPrem : Ctx
    lhsPrem = (B ^ β) ∷ Γ ++ (Γ' -pf (A ^ α))

    eqImpCons : ((((B ⇒ C) ^ β) ∷ Δ) -pf (A ^ α))
             ≡ (((B ⇒ C) ^ β) ∷ (Δ -pf (A ^ α)))
    eqImpCons =
      pf-cons-neq
        {φ = (A ^ α)} {ψ = ((B ⇒ C) ^ β)} {Γ = Δ}
        (λ q → imp≢a (sym q))

    eqImp : (((((B ⇒ C) ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
         ≡ (((B ⇒ C) ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    eqImp = cong (_++ Δ') eqImpCons

    impCase : Dec ((C ^ β) ≡ (A ^ α))
      → Σ (lhs ⊢ ((((B ⇒ C) ^ β) ∷ Δ) -pf (A ^ α) ++ Δ'))
          (λ Π₀ → δ Π₀ ≤ n)

    impCase (yes eqCA) =
      Πres , dΠres≤n
      where
        eqC : ((((C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
           ≡ ((Δ -pf (A ^ α)) ++ Δ')
        eqC = cong (_++ Δ') (pf-cons-eq {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Δ} eqCA)

        Πbase : lhsPrem ⊢ ((Δ -pf (A ^ α)) ++ Δ')
        Πbase = subst (λ xs → lhsPrem ⊢ xs) eqC Π₀

        dΠbase≤n : δ Πbase ≤ n
        dΠbase≤n =
          snd (subst-δ-Δ eqC Π₀ dΠ₀≤n)

        Πweak : lhsPrem ⊢ ((C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πweak = WeakenR Πbase

        Πimp : lhs ⊢ (((B ⇒ C) ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πimp = ImpR Πweak

        Πres : lhs ⊢ ((((B ⇒ C) ^ β) ∷ Δ) -pf (A ^ α) ++ Δ')
        Πres = subst (λ xs → lhs ⊢ xs) (sym eqImp) Πimp

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Δ (sym eqImp) Πimp dΠbase≤n)

    impCase (no c≢a) =
      Πres , dΠres≤n
      where
        eqC : ((((C ^ β) ∷ Δ) -pf (A ^ α)) ++ Δ')
           ≡ ((C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        eqC =
          cong (_++ Δ')
            (pf-cons-neq
              {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Δ}
              (λ q → c≢a (sym q)))

        Πprem : lhsPrem ⊢ ((C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πprem = subst (λ xs → lhsPrem ⊢ xs) eqC Π₀

        dΠprem≤n : δ Πprem ≤ n
        dΠprem≤n =
          snd (subst-δ-Δ eqC Π₀ dΠ₀≤n)

        Πimp : lhs ⊢ (((B ⇒ C) ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πimp = ImpR Πprem

        Πres : lhs ⊢ ((((B ⇒ C) ^ β) ∷ Δ) -pf (A ^ α) ++ Δ')
        Πres = subst (λ xs → lhs ⊢ xs) (sym eqImp) Πimp

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Δ (sym eqImp) Πimp dΠprem≤n)

mix-lift-left-AndR
  {Γ₁} {Γ₂} {Δ₁} {Δ₂} {Γ'} {Δ'} {A} {B} {C} {α} {β}
  and≢a n (Π₁ , dΠ₁≤n) (Π₂ , dΠ₂≤n) =
  Πres , dΠres≤n
  where
    rem : Ctx
    rem = Γ' -pf (A ^ α)

    bPrem :
      Σ ((Γ₁ ++ rem) ⊢ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ')))
        (λ Π₀ → δ Π₀ ≤ n)
    bPrem = bCase ((B ^ β) ≟pf (A ^ α))
      where
        bCase : Dec ((B ^ β) ≡ (A ^ α))
          → Σ ((Γ₁ ++ rem) ⊢ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ')))
              (λ Π₀ → δ Π₀ ≤ n)
        bCase (yes eqBA) = Πweak , dΠbase≤n
          where
            eqB : ((((B ^ β) ∷ Δ₁) -pf (A ^ α)) ++ Δ')
               ≡ ((Δ₁ -pf (A ^ α)) ++ Δ')
            eqB = cong (_++ Δ') (pf-cons-eq {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ₁} eqBA)

            Πbase : (Γ₁ ++ rem) ⊢ ((Δ₁ -pf (A ^ α)) ++ Δ')
            Πbase = subst (λ xs → (Γ₁ ++ rem) ⊢ xs) eqB Π₁

            dΠbase≤n : δ Πbase ≤ n
            dΠbase≤n = snd (subst-δ-Δ eqB Π₁ dΠ₁≤n)

            Πweak : (Γ₁ ++ rem) ⊢ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
            Πweak = WeakenR Πbase

        bCase (no b≢a) = Πprem , dΠprem≤n
          where
            eqB : ((((B ^ β) ∷ Δ₁) -pf (A ^ α)) ++ Δ')
               ≡ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
            eqB =
              cong (_++ Δ')
                (pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ₁}
                  (λ q → b≢a (sym q)))

            Πprem : (Γ₁ ++ rem) ⊢ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
            Πprem = subst (λ xs → (Γ₁ ++ rem) ⊢ xs) eqB Π₁

            dΠprem≤n : δ Πprem ≤ n
            dΠprem≤n = snd (subst-δ-Δ eqB Π₁ dΠ₁≤n)

    cPrem :
      Σ ((Γ₂ ++ rem) ⊢ ((C ^ β) ∷ ((Δ₂ -pf (A ^ α)) ++ Δ')))
        (λ Π₀ → δ Π₀ ≤ n)
    cPrem = cCase ((C ^ β) ≟pf (A ^ α))
      where
        cCase : Dec ((C ^ β) ≡ (A ^ α))
          → Σ ((Γ₂ ++ rem) ⊢ ((C ^ β) ∷ ((Δ₂ -pf (A ^ α)) ++ Δ')))
              (λ Π₀ → δ Π₀ ≤ n)
        cCase (yes eqCA) = Πweak , dΠbase≤n
          where
            eqC : ((((C ^ β) ∷ Δ₂) -pf (A ^ α)) ++ Δ')
               ≡ ((Δ₂ -pf (A ^ α)) ++ Δ')
            eqC = cong (_++ Δ') (pf-cons-eq {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Δ₂} eqCA)

            Πbase : (Γ₂ ++ rem) ⊢ ((Δ₂ -pf (A ^ α)) ++ Δ')
            Πbase = subst (λ xs → (Γ₂ ++ rem) ⊢ xs) eqC Π₂

            dΠbase≤n : δ Πbase ≤ n
            dΠbase≤n = snd (subst-δ-Δ eqC Π₂ dΠ₂≤n)

            Πweak : (Γ₂ ++ rem) ⊢ ((C ^ β) ∷ ((Δ₂ -pf (A ^ α)) ++ Δ'))
            Πweak = WeakenR Πbase

        cCase (no c≢a) = Πprem , dΠprem≤n
          where
            eqC : ((((C ^ β) ∷ Δ₂) -pf (A ^ α)) ++ Δ')
               ≡ ((C ^ β) ∷ ((Δ₂ -pf (A ^ α)) ++ Δ'))
            eqC =
              cong (_++ Δ')
                (pf-cons-neq
                  {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Δ₂}
                  (λ q → c≢a (sym q)))

            Πprem : (Γ₂ ++ rem) ⊢ ((C ^ β) ∷ ((Δ₂ -pf (A ^ α)) ++ Δ'))
            Πprem = subst (λ xs → (Γ₂ ++ rem) ⊢ xs) eqC Π₂

            dΠprem≤n : δ Πprem ≤ n
            dΠprem≤n = snd (subst-δ-Δ eqC Π₂ dΠ₂≤n)

    Πb : (Γ₁ ++ rem) ⊢ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
    Πb = fst bPrem

    dΠb≤n : δ Πb ≤ n
    dΠb≤n = snd bPrem

    Πc : (Γ₂ ++ rem) ⊢ ((C ^ β) ∷ ((Δ₂ -pf (A ^ α)) ++ Δ'))
    Πc = fst cPrem

    dΠc≤n : δ Πc ≤ n
    dΠc≤n = snd cPrem

    Πand₀ : ((Γ₁ ++ rem) ++ (Γ₂ ++ rem))
          ⊢ ((And B C ^ β) ∷ (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ')))
    Πand₀ = AndR Πb Πc

    dΠand₀≤n : δ Πand₀ ≤ n
    dΠand₀≤n = max-least dΠb≤n dΠc≤n

    subL : ((Γ₁ ++ rem) ++ (Γ₂ ++ rem))
       ⊆ ((Γ₁ ++ Γ₂) ++ rem)
    subL = solveCtx⊆!

    rhsMid : Ctx
    rhsMid = (And B C ^ β) ∷ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')

    tailDstExpanded : Ctx
    tailDstExpanded = (((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) ++ Δ')

    tailEq : tailDstExpanded ≡ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')
    tailEq = sym (cong (_++ Δ') (pf-++ (A ^ α) Δ₁ Δ₂))

    tailSubFromLeft : ∀ {y : PFormula}
      → y ∈ ((Δ₁ -pf (A ^ α)) ++ Δ')
      → y ∈ tailDstExpanded
    tailSubFromLeft {y} yInL with ∈-++⁻ (Δ₁ -pf (A ^ α)) {ys = Δ'} yInL
    ... | inl yInΔ₁ = ∈-++⁺ˡ (∈-++⁺ˡ yInΔ₁)
    ... | inr yInΔ' =
      ∈-++⁺ʳ ((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) yInΔ'

    tailSubFromRight : ∀ {y : PFormula}
      → y ∈ ((Δ₂ -pf (A ^ α)) ++ Δ')
      → y ∈ tailDstExpanded
    tailSubFromRight {y} yInR with ∈-++⁻ (Δ₂ -pf (A ^ α)) {ys = Δ'} yInR
    ... | inl yInΔ₂ = ∈-++⁺ˡ (∈-++⁺ʳ (Δ₁ -pf (A ^ α)) yInΔ₂)
    ... | inr yInΔ' =
      ∈-++⁺ʳ ((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) yInΔ'

    tailSubExpanded :
      (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ'))
      ⊆ tailDstExpanded
    tailSubExpanded {y} yIn with ∈-++⁻ ((Δ₁ -pf (A ^ α)) ++ Δ') {ys = ((Δ₂ -pf (A ^ α)) ++ Δ')} yIn
    ... | inl yInL = tailSubFromLeft yInL
    ... | inr yInR = tailSubFromRight yInR

    tailSub :
      (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ'))
      ⊆ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')
    tailSub {y} yIn = subst (y ∈_) tailEq (tailSubExpanded yIn)

    subD :
      ((And B C ^ β) ∷ (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ')))
      ⊆ rhsMid
    subD {y} yIn with yIn
    ... | here y≡And = here y≡And
    ... | there yInTail = there (tailSub yInTail)

    Πmid : ((Γ₁ ++ Γ₂) ++ rem) ⊢ rhsMid
    Πmid = structural subL subD Πand₀

    dΠmid≤n : δ Πmid ≤ n
    dΠmid≤n =
      snd (structural-δ subL subD Πand₀ dΠand₀≤n)

    eqAnd : ((((And B C ^ β) ∷ (Δ₁ ++ Δ₂)) -pf (A ^ α)) ++ Δ')
         ≡ rhsMid
    eqAnd =
      cong (_++ Δ')
        (pf-cons-neq
          {φ = (A ^ α)} {ψ = (And B C ^ β)} {Γ = (Δ₁ ++ Δ₂)}
          (λ q → and≢a (sym q)))

    Πres : ((Γ₁ ++ Γ₂) ++ rem)
       ⊢ ((((And B C ^ β) ∷ (Δ₁ ++ Δ₂)) -pf (A ^ α)) ++ Δ')
    Πres = subst (λ xs → ((Γ₁ ++ Γ₂) ++ rem) ⊢ xs) (sym eqAnd) Πmid

    dΠres≤n : δ Πres ≤ n
    dΠres≤n =
      snd (subst-δ-Δ (sym eqAnd) Πmid dΠmid≤n)

mix-lift-left-OrL
  {Γ₁} {Γ₂} {Δ₁} {Δ₂} {Γ'} {Δ'} {A} {B} {C} {α} {β}
  or≢a n (Π₁ , dΠ₁≤n) (Π₂ , dΠ₂≤n) =
  Πres , dΠres≤n
  where
    rem : Ctx
    rem = Γ' -pf (A ^ α)

    subLB : (((B ^ β) ∷ Γ₁) ++ rem) ⊆ ((B ^ β) ∷ (Γ₁ ++ rem))
    subLB = solveCtx⊆!

    Πb : ((B ^ β) ∷ (Γ₁ ++ rem)) ⊢ ((Δ₁ -pf (A ^ α)) ++ Δ')
    Πb = structural subLB subset-refl Π₁

    dΠb≤n : δ Πb ≤ n
    dΠb≤n = snd (structural-δ subLB subset-refl Π₁ dΠ₁≤n)

    subLC : (((C ^ β) ∷ Γ₂) ++ rem) ⊆ ((C ^ β) ∷ (Γ₂ ++ rem))
    subLC = solveCtx⊆!

    Πc : ((C ^ β) ∷ (Γ₂ ++ rem)) ⊢ ((Δ₂ -pf (A ^ α)) ++ Δ')
    Πc = structural subLC subset-refl Π₂

    dΠc≤n : δ Πc ≤ n
    dΠc≤n = snd (structural-δ subLC subset-refl Π₂ dΠ₂≤n)

    Πor₀ : ((Or B C ^ β) ∷ ((Γ₁ ++ rem) ++ (Γ₂ ++ rem)))
         ⊢ (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ'))
    Πor₀ = OrL Πb Πc

    dΠor₀≤n : δ Πor₀ ≤ n
    dΠor₀≤n = max-least dΠb≤n dΠc≤n

    subL : ((Or B C ^ β) ∷ ((Γ₁ ++ rem) ++ (Γ₂ ++ rem)))
       ⊆ (((Or B C ^ β) ∷ (Γ₁ ++ Γ₂)) ++ rem)
    subL = solveCtx⊆!

    tailDstExpanded : Ctx
    tailDstExpanded = (((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) ++ Δ')

    tailEq : tailDstExpanded ≡ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')
    tailEq = sym (cong (_++ Δ') (pf-++ (A ^ α) Δ₁ Δ₂))

    tailSubFromLeft : ∀ {y : PFormula}
      → y ∈ ((Δ₁ -pf (A ^ α)) ++ Δ')
      → y ∈ tailDstExpanded
    tailSubFromLeft {y} yInL with ∈-++⁻ (Δ₁ -pf (A ^ α)) {ys = Δ'} yInL
    ... | inl yInΔ₁ = ∈-++⁺ˡ (∈-++⁺ˡ yInΔ₁)
    ... | inr yInΔ' =
      ∈-++⁺ʳ ((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) yInΔ'

    tailSubFromRight : ∀ {y : PFormula}
      → y ∈ ((Δ₂ -pf (A ^ α)) ++ Δ')
      → y ∈ tailDstExpanded
    tailSubFromRight {y} yInR with ∈-++⁻ (Δ₂ -pf (A ^ α)) {ys = Δ'} yInR
    ... | inl yInΔ₂ = ∈-++⁺ˡ (∈-++⁺ʳ (Δ₁ -pf (A ^ α)) yInΔ₂)
    ... | inr yInΔ' =
      ∈-++⁺ʳ ((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) yInΔ'

    subDExpanded :
      (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ'))
      ⊆ tailDstExpanded
    subDExpanded {y} yIn with ∈-++⁻ ((Δ₁ -pf (A ^ α)) ++ Δ') {ys = ((Δ₂ -pf (A ^ α)) ++ Δ')} yIn
    ... | inl yInL = tailSubFromLeft yInL
    ... | inr yInR = tailSubFromRight yInR

    subD : (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ'))
       ⊆ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')
    subD {y} yIn = subst (y ∈_) tailEq (subDExpanded yIn)

    Πres : (((Or B C ^ β) ∷ (Γ₁ ++ Γ₂)) ++ rem)
       ⊢ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')
    Πres = structural subL subD Πor₀

    dΠres≤n : δ Πres ≤ n
    dΠres≤n =
      snd (structural-δ subL subD Πor₀ dΠor₀≤n)

mix-lift-left-ImpL
  {Γ₁} {Γ₂} {Δ₁} {Δ₂} {Γ'} {Δ'} {A} {B} {C} {α} {β}
  imp≢a n (Π₁ , dΠ₁≤n) (Π₂ , dΠ₂≤n) =
  Πres , dΠres≤n
  where
    rem : Ctx
    rem = Γ' -pf (A ^ α)

    bPrem :
      Σ ((Γ₁ ++ rem) ⊢ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ')))
        (λ Π₀ → δ Π₀ ≤ n)
    bPrem = bCase ((B ^ β) ≟pf (A ^ α))
      where
        bCase : Dec ((B ^ β) ≡ (A ^ α))
          → Σ ((Γ₁ ++ rem) ⊢ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ')))
              (λ Π₀ → δ Π₀ ≤ n)
        bCase (yes eqBA) = Πweak , dΠbase≤n
          where
            eqB : ((((B ^ β) ∷ Δ₁) -pf (A ^ α)) ++ Δ')
               ≡ ((Δ₁ -pf (A ^ α)) ++ Δ')
            eqB = cong (_++ Δ') (pf-cons-eq {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ₁} eqBA)

            Πbase : (Γ₁ ++ rem) ⊢ ((Δ₁ -pf (A ^ α)) ++ Δ')
            Πbase = subst (λ xs → (Γ₁ ++ rem) ⊢ xs) eqB Π₁

            dΠbase≤n : δ Πbase ≤ n
            dΠbase≤n = snd (subst-δ-Δ eqB Π₁ dΠ₁≤n)

            Πweak : (Γ₁ ++ rem) ⊢ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
            Πweak = WeakenR Πbase

        bCase (no b≢a) = Πprem , dΠprem≤n
          where
            eqB : ((((B ^ β) ∷ Δ₁) -pf (A ^ α)) ++ Δ')
               ≡ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
            eqB =
              cong (_++ Δ')
                (pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Δ₁}
                  (λ q → b≢a (sym q)))

            Πprem : (Γ₁ ++ rem) ⊢ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
            Πprem = subst (λ xs → (Γ₁ ++ rem) ⊢ xs) eqB Π₁

            dΠprem≤n : δ Πprem ≤ n
            dΠprem≤n = snd (subst-δ-Δ eqB Π₁ dΠ₁≤n)

    subLC : (((C ^ β) ∷ Γ₂) ++ rem) ⊆ ((C ^ β) ∷ (Γ₂ ++ rem))
    subLC = solveCtx⊆!

    Πc : ((C ^ β) ∷ (Γ₂ ++ rem)) ⊢ ((Δ₂ -pf (A ^ α)) ++ Δ')
    Πc = structural subLC subset-refl Π₂

    dΠc≤n : δ Πc ≤ n
    dΠc≤n = snd (structural-δ subLC subset-refl Π₂ dΠ₂≤n)

    Πb : (Γ₁ ++ rem) ⊢ ((B ^ β) ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
    Πb = fst bPrem

    dΠb≤n : δ Πb ≤ n
    dΠb≤n = snd bPrem

    Πimp₀ : (((B ⇒ C) ^ β) ∷ ((Γ₁ ++ rem) ++ (Γ₂ ++ rem)))
         ⊢ (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ'))
    Πimp₀ = ImpL Πb Πc

    dΠimp₀≤n : δ Πimp₀ ≤ n
    dΠimp₀≤n = max-least dΠb≤n dΠc≤n

    subL : (((B ⇒ C) ^ β) ∷ ((Γ₁ ++ rem) ++ (Γ₂ ++ rem)))
       ⊆ ((((B ⇒ C) ^ β) ∷ (Γ₁ ++ Γ₂)) ++ rem)
    subL = solveCtx⊆!

    tailDstExpanded : Ctx
    tailDstExpanded = (((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) ++ Δ')

    tailEq : tailDstExpanded ≡ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')
    tailEq = sym (cong (_++ Δ') (pf-++ (A ^ α) Δ₁ Δ₂))

    tailSubFromLeft : ∀ {y : PFormula}
      → y ∈ ((Δ₁ -pf (A ^ α)) ++ Δ')
      → y ∈ tailDstExpanded
    tailSubFromLeft {y} yInL with ∈-++⁻ (Δ₁ -pf (A ^ α)) {ys = Δ'} yInL
    ... | inl yInΔ₁ = ∈-++⁺ˡ (∈-++⁺ˡ yInΔ₁)
    ... | inr yInΔ' =
      ∈-++⁺ʳ ((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) yInΔ'

    tailSubFromRight : ∀ {y : PFormula}
      → y ∈ ((Δ₂ -pf (A ^ α)) ++ Δ')
      → y ∈ tailDstExpanded
    tailSubFromRight {y} yInR with ∈-++⁻ (Δ₂ -pf (A ^ α)) {ys = Δ'} yInR
    ... | inl yInΔ₂ = ∈-++⁺ˡ (∈-++⁺ʳ (Δ₁ -pf (A ^ α)) yInΔ₂)
    ... | inr yInΔ' =
      ∈-++⁺ʳ ((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) yInΔ'

    subDExpanded :
      (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ'))
      ⊆ tailDstExpanded
    subDExpanded {y} yIn with ∈-++⁻ ((Δ₁ -pf (A ^ α)) ++ Δ') {ys = ((Δ₂ -pf (A ^ α)) ++ Δ')} yIn
    ... | inl yInL = tailSubFromLeft yInL
    ... | inr yInR = tailSubFromRight yInR

    subD : (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ'))
       ⊆ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')
    subD {y} yIn = subst (y ∈_) tailEq (subDExpanded yIn)

    Πres : ((((B ⇒ C) ^ β) ∷ (Γ₁ ++ Γ₂)) ++ rem)
       ⊢ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')
    Πres = structural subL subD Πimp₀

    dΠres≤n : δ Πres ≤ n
    dΠres≤n =
      snd (structural-δ subL subD Πimp₀ dΠimp₀≤n)

mix-lift-left-Cut
  {Γ₁} {Γ₂} {Δ₁} {Δ₂} {Γ'} {Δ'} {A} {A'} {α} {α'}
  cCut' n dA'≤n (Π₁ , dΠ₁≤n) (Π₂ , dΠ₂≤n) =
  Πres , dΠres≤n
  where
    rem : Ctx
    rem = Γ' -pf (A ^ α)

    aPrem :
      Σ ((Γ₁ ++ rem) ⊢ ((A' ^ α') ∷ ((Δ₁ -pf (A ^ α)) ++ Δ')))
        (λ Π₀ → δ Π₀ ≤ n)
    aPrem = aCase ((A' ^ α') ≟pf (A ^ α))
      where
        aCase : Dec ((A' ^ α') ≡ (A ^ α))
          → Σ ((Γ₁ ++ rem) ⊢ ((A' ^ α') ∷ ((Δ₁ -pf (A ^ α)) ++ Δ')))
              (λ Π₀ → δ Π₀ ≤ n)
        aCase (yes eqAA) = Πweak , dΠbase≤n
          where
            eqA : ((([ (A' ^ α') ] ++ Δ₁) -pf (A ^ α)) ++ Δ')
               ≡ ((Δ₁ -pf (A ^ α)) ++ Δ')
            eqA =
              cong (_++ Δ')
                (pf-cons-eq {φ = (A ^ α)} {ψ = (A' ^ α')} {Γ = Δ₁} eqAA)

            Πbase : (Γ₁ ++ rem) ⊢ ((Δ₁ -pf (A ^ α)) ++ Δ')
            Πbase = subst (λ xs → (Γ₁ ++ rem) ⊢ xs) eqA Π₁

            dΠbase≤n : δ Πbase ≤ n
            dΠbase≤n = snd (subst-δ-Δ eqA Π₁ dΠ₁≤n)

            Πweak : (Γ₁ ++ rem) ⊢ ((A' ^ α') ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
            Πweak = WeakenR Πbase

        aCase (no a'≢a) = Πprem , dΠprem≤n
          where
            eqA : ((([ (A' ^ α') ] ++ Δ₁) -pf (A ^ α)) ++ Δ')
               ≡ ((A' ^ α') ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
            eqA =
              cong (_++ Δ')
                (pf-cons-neq
                  {φ = (A ^ α)} {ψ = (A' ^ α')} {Γ = Δ₁}
                  (λ q → a'≢a (sym q)))

            Πprem : (Γ₁ ++ rem) ⊢ ((A' ^ α') ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
            Πprem = subst (λ xs → (Γ₁ ++ rem) ⊢ xs) eqA Π₁

            dΠprem≤n : δ Πprem ≤ n
            dΠprem≤n = snd (subst-δ-Δ eqA Π₁ dΠ₁≤n)

    Πa : (Γ₁ ++ rem) ⊢ ((A' ^ α') ∷ ((Δ₁ -pf (A ^ α)) ++ Δ'))
    Πa = fst aPrem

    dΠa≤n : δ Πa ≤ n
    dΠa≤n = snd aPrem

    subL₂ : ((Γ₂ ++ [ (A' ^ α') ]) ++ rem) ⊆ ((Γ₂ ++ rem) ++ [ (A' ^ α') ])
    subL₂ = solveCtx⊆!

    Π₂cut : ((Γ₂ ++ rem) ++ [ (A' ^ α') ]) ⊢ ((Δ₂ -pf (A ^ α)) ++ Δ')
    Π₂cut = structural subL₂ subset-refl Π₂

    dΠ₂cut≤n : δ Π₂cut ≤ n
    dΠ₂cut≤n = snd (structural-δ subL₂ subset-refl Π₂ dΠ₂≤n)

    Πcut₀ : ((Γ₁ ++ rem) ++ (Γ₂ ++ rem))
         ⊢ (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ'))
    Πcut₀ = Cut cCut' Πa Π₂cut

    dΠcut₀≤n : δ Πcut₀ ≤ n
    dΠcut₀≤n = max-least dA'≤n (max-least dΠa≤n dΠ₂cut≤n)

    subL : ((Γ₁ ++ rem) ++ (Γ₂ ++ rem))
       ⊆ ((Γ₁ ++ Γ₂) ++ rem)
    subL = solveCtx⊆!

    tailDstExpanded : Ctx
    tailDstExpanded = (((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) ++ Δ')

    tailEq : tailDstExpanded ≡ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')
    tailEq = sym (cong (_++ Δ') (pf-++ (A ^ α) Δ₁ Δ₂))

    tailSubFromLeft : ∀ {y : PFormula}
      → y ∈ ((Δ₁ -pf (A ^ α)) ++ Δ')
      → y ∈ tailDstExpanded
    tailSubFromLeft {y} yInL with ∈-++⁻ (Δ₁ -pf (A ^ α)) {ys = Δ'} yInL
    ... | inl yInΔ₁ = ∈-++⁺ˡ (∈-++⁺ˡ yInΔ₁)
    ... | inr yInΔ' =
      ∈-++⁺ʳ ((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) yInΔ'

    tailSubFromRight : ∀ {y : PFormula}
      → y ∈ ((Δ₂ -pf (A ^ α)) ++ Δ')
      → y ∈ tailDstExpanded
    tailSubFromRight {y} yInR with ∈-++⁻ (Δ₂ -pf (A ^ α)) {ys = Δ'} yInR
    ... | inl yInΔ₂ = ∈-++⁺ˡ (∈-++⁺ʳ (Δ₁ -pf (A ^ α)) yInΔ₂)
    ... | inr yInΔ' =
      ∈-++⁺ʳ ((Δ₁ -pf (A ^ α)) ++ (Δ₂ -pf (A ^ α))) yInΔ'

    subDExpanded :
      (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ'))
      ⊆ tailDstExpanded
    subDExpanded {y} yIn with ∈-++⁻ ((Δ₁ -pf (A ^ α)) ++ Δ') {ys = ((Δ₂ -pf (A ^ α)) ++ Δ')} yIn
    ... | inl yInL = tailSubFromLeft yInL
    ... | inr yInR = tailSubFromRight yInR

    subD : (((Δ₁ -pf (A ^ α)) ++ Δ') ++ ((Δ₂ -pf (A ^ α)) ++ Δ'))
       ⊆ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')
    subD {y} yIn = subst (y ∈_) tailEq (subDExpanded yIn)

    Πres : ((Γ₁ ++ Γ₂) ++ rem) ⊢ (((Δ₁ ++ Δ₂) -pf (A ^ α)) ++ Δ')
    Πres = structural subL subD Πcut₀

    dΠres≤n : δ Πres ≤ n
    dΠres≤n =
      snd (structural-δ subL subD Πcut₀ dΠcut₀≤n)

mix-lift-left-BoxL
  {Γ} {Δ} {Γ'} {Δ'} {A} {B} {α} {β} {γ}
  box≢a mc' n (Π₀ , dΠ₀≤n) =
  Πres , dΠres≤n
  where
    rem : Ctx
    rem = Γ' -pf (A ^ α)

    subL₁ : ((Γ ++ [ (B ^ γ) ]) ++ rem) ⊆ ((Γ ++ rem) ++ [ (B ^ γ) ])
    subL₁ = solveCtx⊆!

    Π₁ : ((Γ ++ rem) ++ [ (B ^ γ) ]) ⊢ ((Δ -pf (A ^ α)) ++ Δ')
    Π₁ = structural subL₁ subset-refl Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subL₁ subset-refl Π₀ dΠ₀≤n)

    Πbox : ((Γ ++ rem) ++ [ (□ B ^ β) ]) ⊢ ((Δ -pf (A ^ α)) ++ Δ')
    Πbox = BoxL mc' Π₁

    subL₂ : ((Γ ++ rem) ++ [ (□ B ^ β) ]) ⊆ ((Γ ++ [ (□ B ^ β) ]) ++ rem)
    subL₂ = solveCtx⊆!

    Πres : ((Γ ++ [ (□ B ^ β) ]) ++ rem) ⊢ ((Δ -pf (A ^ α)) ++ Δ')
    Πres = structural subL₂ subset-refl Πbox

    dΠres≤n : δ Πres ≤ n
    dΠres≤n =
      snd (structural-δ subL₂ subset-refl Πbox dΠ₁≤n)

mix-lift-left-DiaR
  {Γ} {Δ} {Γ'} {Δ'} {A} {B} {α} {β} {γ}
  dia≢a mc' n (Π₀ , dΠ₀≤n) =
  diaCase ((B ^ γ) ≟pf (A ^ α))
  where
    rem : Ctx
    rem = Γ' -pf (A ^ α)

    lhs : Ctx
    lhs = Γ ++ rem

    eqDia : ((([ (♢ B ^ β) ] ++ Δ) -pf (A ^ α)) ++ Δ')
         ≡ ((♢ B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    eqDia =
      cong (_++ Δ')
        (pf-cons-neq
          {φ = (A ^ α)} {ψ = (♢ B ^ β)} {Γ = Δ}
          (λ q → dia≢a (sym q)))

    diaCase : Dec ((B ^ γ) ≡ (A ^ α))
      → Σ (lhs ⊢ ((([ (♢ B ^ β) ] ++ Δ) -pf (A ^ α)) ++ Δ'))
          (λ Π₀ → δ Π₀ ≤ n)

    diaCase (yes eqBA) =
      Πres , dΠres≤n
      where
        eqB : ((([ (B ^ γ) ] ++ Δ) -pf (A ^ α)) ++ Δ')
           ≡ ((Δ -pf (A ^ α)) ++ Δ')
        eqB =
          cong (_++ Δ')
            (pf-cons-eq
              {φ = (A ^ α)} {ψ = (B ^ γ)} {Γ = Δ}
              eqBA)

        Πbase : lhs ⊢ ((Δ -pf (A ^ α)) ++ Δ')
        Πbase = subst (λ xs → lhs ⊢ xs) eqB Π₀

        dΠbase≤n : δ Πbase ≤ n
        dΠbase≤n =
          snd (subst-δ-Δ eqB Π₀ dΠ₀≤n)

        Πprem : lhs ⊢ ((B ^ γ) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πprem = WeakenR Πbase

        Πdia : lhs ⊢ ((♢ B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πdia = DiaR mc' Πprem

        Πres : lhs ⊢ ((([ (♢ B ^ β) ] ++ Δ) -pf (A ^ α)) ++ Δ')
        Πres = subst (λ xs → lhs ⊢ xs) (sym eqDia) Πdia

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Δ (sym eqDia) Πdia dΠbase≤n)

    diaCase (no b≢a) =
      Πres , dΠres≤n
      where
        eqB : ((([ (B ^ γ) ] ++ Δ) -pf (A ^ α)) ++ Δ')
           ≡ ((B ^ γ) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        eqB =
          cong (_++ Δ')
            (pf-cons-neq
              {φ = (A ^ α)} {ψ = (B ^ γ)} {Γ = Δ}
              (λ q → b≢a (sym q)))

        Πprem : lhs ⊢ ((B ^ γ) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πprem = subst (λ xs → lhs ⊢ xs) eqB Π₀

        dΠprem≤n : δ Πprem ≤ n
        dΠprem≤n =
          snd (subst-δ-Δ eqB Π₀ dΠ₀≤n)

        Πdia : lhs ⊢ ((♢ B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πdia = DiaR mc' Πprem

        Πres : lhs ⊢ ((([ (♢ B ^ β) ] ++ Δ) -pf (A ^ α)) ++ Δ')
        Πres = subst (λ xs → lhs ⊢ xs) (sym eqDia) Πdia

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Δ (sym eqDia) Πdia dΠprem≤n)

mix-lift-right-NotL {Γ} {Δ} {Γ'} {Δ'} {A} {B} {α} {β} not≢a n (Π₀ , dΠ₀≤n) =
  Πres , dΠres≤n
  where
    lhs : Ctx
    lhs = Γ ++ (Γ' -pf (A ^ α))

    rhsWithB : Ctx
    rhsWithB = (Δ -pf (A ^ α)) ++ ((B ^ β) ∷ Δ')

    subD₁ : rhsWithB ⊆ ((B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    subD₁ = subset-append-mid-cons (Δ -pf (A ^ α)) Δ' (B ^ β)

    Π₁ : lhs ⊢ ((B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    Π₁ = structural subset-refl subD₁ Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subset-refl subD₁ Π₀ dΠ₀≤n)

    Π₂ : ((Not B ^ β) ∷ lhs) ⊢ ((Δ -pf (A ^ α)) ++ Δ')
    Π₂ = NotL Π₁

    eqAntRem : (((Not B ^ β) ∷ Γ') -pf (A ^ α))
            ≡ ((Not B ^ β) ∷ (Γ' -pf (A ^ α)))
    eqAntRem =
      pf-cons-neq
        {φ = (A ^ α)} {ψ = (Not B ^ β)} {Γ = Γ'}
        (λ q → not≢a (sym q))

    subL : ((Not B ^ β) ∷ (Γ ++ (Γ' -pf (A ^ α))))
        ⊆ (Γ ++ ((Not B ^ β) ∷ (Γ' -pf (A ^ α))))
    subL = subset-cons-append-mid Γ (Γ' -pf (A ^ α)) (Not B ^ β)

    Π₃ : (Γ ++ ((Not B ^ β) ∷ (Γ' -pf (A ^ α))))
       ⊢ ((Δ -pf (A ^ α)) ++ Δ')
    Π₃ = structural subL subset-refl Π₂

    dΠ₃≤n : δ Π₃ ≤ n
    dΠ₃≤n =
      snd (structural-δ subL subset-refl Π₂ dΠ₁≤n)

    eqAntCtx : (Γ ++ ((Not B ^ β) ∷ (Γ' -pf (A ^ α))))
            ≡ (Γ ++ (((Not B ^ β) ∷ Γ') -pf (A ^ α)))
    eqAntCtx = cong (Γ ++_) (sym eqAntRem)

    Πres : (Γ ++ (((Not B ^ β) ∷ Γ') -pf (A ^ α)))
       ⊢ ((Δ -pf (A ^ α)) ++ Δ')
    Πres = subst (λ xs → xs ⊢ ((Δ -pf (A ^ α)) ++ Δ')) eqAntCtx Π₃

    dΠres≤n : δ Πres ≤ n
    dΠres≤n =
      snd (subst-δ-Γ eqAntCtx Π₃ dΠ₃≤n)

mix-lift-right-AndL1 {Γ} {Δ} {Γ'} {Δ'} {A} {B} {C} {α} {β} and≢a n (Π₀ , dΠ₀≤n) =
  bCase ((B ^ β) ≟pf (A ^ α))
  where
    rhs : Ctx
    rhs = (Δ -pf (A ^ α)) ++ Δ'

    rem : Ctx
    rem = Γ' -pf (A ^ α)

    target : Ctx
    target = Γ ++ (((And B C ^ β) ∷ Γ') -pf (A ^ α))

    bCase : Dec ((B ^ β) ≡ (A ^ α))
      → Σ (target ⊢ rhs)
          (λ Π₀ → δ Π₀ ≤ n)

    bCase (yes eqBA) =
      Πres , dΠres≤n
      where
        eqAnt : (((B ^ β) ∷ Γ') -pf (A ^ α))
             ≡ (Γ' -pf (A ^ α))
        eqAnt = pf-cons-eq {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'} eqBA

        eqAntCtx : (Γ ++ (((B ^ β) ∷ Γ') -pf (A ^ α))) ≡ (Γ ++ rem)
        eqAntCtx = cong (Γ ++_) eqAnt

        Πbase : (Γ ++ rem) ⊢ rhs
        Πbase = subst (λ xs → xs ⊢ rhs) eqAntCtx Π₀

        dΠbase≤n : δ Πbase ≤ n
        dΠbase≤n =
          snd (subst-δ-Γ eqAntCtx Π₀ dΠ₀≤n)

        Πprem : ((B ^ β) ∷ (Γ ++ rem)) ⊢ rhs
        Πprem = WeakenL Πbase

        Πand₀ : ((And B C ^ β) ∷ (Γ ++ rem)) ⊢ rhs
        Πand₀ = AndL1 Πprem

        subL₁ : ((And B C ^ β) ∷ (Γ ++ rem))
            ⊆ (Γ ++ ((And B C ^ β) ∷ rem))
        subL₁ = subset-cons-append-mid Γ rem (And B C ^ β)

        Πand₁ : (Γ ++ ((And B C ^ β) ∷ rem)) ⊢ rhs
        Πand₁ = structural subL₁ subset-refl Πand₀

        dΠand₁≤n : δ Πand₁ ≤ n
        dΠand₁≤n =
          snd (structural-δ subL₁ subset-refl Πand₀ dΠbase≤n)

        eqRem : (((And B C ^ β) ∷ Γ') -pf (A ^ α))
            ≡ ((And B C ^ β) ∷ rem)
        eqRem =
          pf-cons-neq
            {φ = (A ^ α)} {ψ = (And B C ^ β)} {Γ = Γ'}
            (λ q → and≢a (sym q))

        eqCtx : (Γ ++ ((And B C ^ β) ∷ rem))
            ≡ (Γ ++ (((And B C ^ β) ∷ Γ') -pf (A ^ α)))
        eqCtx = cong (Γ ++_) (sym eqRem)

        Πres : target ⊢ rhs
        Πres = subst (λ xs → xs ⊢ rhs) eqCtx Πand₁

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Γ eqCtx Πand₁ dΠand₁≤n)

    bCase (no b≢a) =
      Πres , dΠres≤n
      where
        eqAnt : (((B ^ β) ∷ Γ') -pf (A ^ α))
             ≡ ((B ^ β) ∷ rem)
        eqAnt =
          pf-cons-neq
            {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'}
            (λ q → b≢a (sym q))

        eqAntCtx : (Γ ++ (((B ^ β) ∷ Γ') -pf (A ^ α)))
               ≡ (Γ ++ ((B ^ β) ∷ rem))
        eqAntCtx = cong (Γ ++_) eqAnt

        Πmid₀ : (Γ ++ ((B ^ β) ∷ rem)) ⊢ rhs
        Πmid₀ = subst (λ xs → xs ⊢ rhs) eqAntCtx Π₀

        dΠmid₀≤n : δ Πmid₀ ≤ n
        dΠmid₀≤n =
          snd (subst-δ-Γ eqAntCtx Π₀ dΠ₀≤n)

        subLB : (Γ ++ ((B ^ β) ∷ rem))
            ⊆ ((B ^ β) ∷ (Γ ++ rem))
        subLB = subset-append-mid-cons Γ rem (B ^ β)

        Πprem : ((B ^ β) ∷ (Γ ++ rem)) ⊢ rhs
        Πprem = structural subLB subset-refl Πmid₀

        dΠprem≤n : δ Πprem ≤ n
        dΠprem≤n =
          snd (structural-δ subLB subset-refl Πmid₀ dΠmid₀≤n)

        Πand₀ : ((And B C ^ β) ∷ (Γ ++ rem)) ⊢ rhs
        Πand₀ = AndL1 Πprem

        subL₁ : ((And B C ^ β) ∷ (Γ ++ rem))
            ⊆ (Γ ++ ((And B C ^ β) ∷ rem))
        subL₁ = subset-cons-append-mid Γ rem (And B C ^ β)

        Πand₁ : (Γ ++ ((And B C ^ β) ∷ rem)) ⊢ rhs
        Πand₁ = structural subL₁ subset-refl Πand₀

        dΠand₁≤n : δ Πand₁ ≤ n
        dΠand₁≤n =
          snd (structural-δ subL₁ subset-refl Πand₀ dΠprem≤n)

        eqRem : (((And B C ^ β) ∷ Γ') -pf (A ^ α))
            ≡ ((And B C ^ β) ∷ rem)
        eqRem =
          pf-cons-neq
            {φ = (A ^ α)} {ψ = (And B C ^ β)} {Γ = Γ'}
            (λ q → and≢a (sym q))

        eqCtx : (Γ ++ ((And B C ^ β) ∷ rem))
            ≡ target
        eqCtx = cong (Γ ++_) (sym eqRem)

        Πres : target ⊢ rhs
        Πres = subst (λ xs → xs ⊢ rhs) eqCtx Πand₁

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Γ eqCtx Πand₁ dΠand₁≤n)

mix-lift-right-AndL2 {Γ} {Δ} {Γ'} {Δ'} {A} {B} {C} {α} {β} and≢a n (Π₀ , dΠ₀≤n) =
  cCase ((C ^ β) ≟pf (A ^ α))
  where
    rhs : Ctx
    rhs = (Δ -pf (A ^ α)) ++ Δ'

    rem : Ctx
    rem = Γ' -pf (A ^ α)

    target : Ctx
    target = Γ ++ (((And B C ^ β) ∷ Γ') -pf (A ^ α))

    cCase : Dec ((C ^ β) ≡ (A ^ α))
      → Σ (target ⊢ rhs)
          (λ Π₀ → δ Π₀ ≤ n)

    cCase (yes eqCA) =
      Πres , dΠres≤n
      where
        eqAnt : (((C ^ β) ∷ Γ') -pf (A ^ α))
             ≡ (Γ' -pf (A ^ α))
        eqAnt = pf-cons-eq {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Γ'} eqCA

        eqAntCtx : (Γ ++ (((C ^ β) ∷ Γ') -pf (A ^ α))) ≡ (Γ ++ rem)
        eqAntCtx = cong (Γ ++_) eqAnt

        Πbase : (Γ ++ rem) ⊢ rhs
        Πbase = subst (λ xs → xs ⊢ rhs) eqAntCtx Π₀

        dΠbase≤n : δ Πbase ≤ n
        dΠbase≤n =
          snd (subst-δ-Γ eqAntCtx Π₀ dΠ₀≤n)

        Πprem : ((C ^ β) ∷ (Γ ++ rem)) ⊢ rhs
        Πprem = WeakenL Πbase

        Πand₀ : ((And B C ^ β) ∷ (Γ ++ rem)) ⊢ rhs
        Πand₀ = AndL2 Πprem

        subL₁ : ((And B C ^ β) ∷ (Γ ++ rem))
            ⊆ (Γ ++ ((And B C ^ β) ∷ rem))
        subL₁ = subset-cons-append-mid Γ rem (And B C ^ β)

        Πand₁ : (Γ ++ ((And B C ^ β) ∷ rem)) ⊢ rhs
        Πand₁ = structural subL₁ subset-refl Πand₀

        dΠand₁≤n : δ Πand₁ ≤ n
        dΠand₁≤n =
          snd (structural-δ subL₁ subset-refl Πand₀ dΠbase≤n)

        eqRem : (((And B C ^ β) ∷ Γ') -pf (A ^ α))
            ≡ ((And B C ^ β) ∷ rem)
        eqRem =
          pf-cons-neq
            {φ = (A ^ α)} {ψ = (And B C ^ β)} {Γ = Γ'}
            (λ q → and≢a (sym q))

        eqCtx : (Γ ++ ((And B C ^ β) ∷ rem))
            ≡ (Γ ++ (((And B C ^ β) ∷ Γ') -pf (A ^ α)))
        eqCtx = cong (Γ ++_) (sym eqRem)

        Πres : target ⊢ rhs
        Πres = subst (λ xs → xs ⊢ rhs) eqCtx Πand₁

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Γ eqCtx Πand₁ dΠand₁≤n)

    cCase (no c≢a) =
      Πres , dΠres≤n
      where
        eqAnt : (((C ^ β) ∷ Γ') -pf (A ^ α))
             ≡ ((C ^ β) ∷ rem)
        eqAnt =
          pf-cons-neq
            {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Γ'}
            (λ q → c≢a (sym q))

        eqAntCtx : (Γ ++ (((C ^ β) ∷ Γ') -pf (A ^ α)))
               ≡ (Γ ++ ((C ^ β) ∷ rem))
        eqAntCtx = cong (Γ ++_) eqAnt

        Πmid₀ : (Γ ++ ((C ^ β) ∷ rem)) ⊢ rhs
        Πmid₀ = subst (λ xs → xs ⊢ rhs) eqAntCtx Π₀

        dΠmid₀≤n : δ Πmid₀ ≤ n
        dΠmid₀≤n =
          snd (subst-δ-Γ eqAntCtx Π₀ dΠ₀≤n)

        subLC : (Γ ++ ((C ^ β) ∷ rem))
            ⊆ ((C ^ β) ∷ (Γ ++ rem))
        subLC = subset-append-mid-cons Γ rem (C ^ β)

        Πprem : ((C ^ β) ∷ (Γ ++ rem)) ⊢ rhs
        Πprem = structural subLC subset-refl Πmid₀

        dΠprem≤n : δ Πprem ≤ n
        dΠprem≤n =
          snd (structural-δ subLC subset-refl Πmid₀ dΠmid₀≤n)

        Πand₀ : ((And B C ^ β) ∷ (Γ ++ rem)) ⊢ rhs
        Πand₀ = AndL2 Πprem

        subL₁ : ((And B C ^ β) ∷ (Γ ++ rem))
            ⊆ (Γ ++ ((And B C ^ β) ∷ rem))
        subL₁ = subset-cons-append-mid Γ rem (And B C ^ β)

        Πand₁ : (Γ ++ ((And B C ^ β) ∷ rem)) ⊢ rhs
        Πand₁ = structural subL₁ subset-refl Πand₀

        dΠand₁≤n : δ Πand₁ ≤ n
        dΠand₁≤n =
          snd (structural-δ subL₁ subset-refl Πand₀ dΠprem≤n)

        eqRem : (((And B C ^ β) ∷ Γ') -pf (A ^ α))
            ≡ ((And B C ^ β) ∷ rem)
        eqRem =
          pf-cons-neq
            {φ = (A ^ α)} {ψ = (And B C ^ β)} {Γ = Γ'}
            (λ q → and≢a (sym q))

        eqCtx : (Γ ++ ((And B C ^ β) ∷ rem))
            ≡ target
        eqCtx = cong (Γ ++_) (sym eqRem)

        Πres : target ⊢ rhs
        Πres = subst (λ xs → xs ⊢ rhs) eqCtx Πand₁

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Γ eqCtx Πand₁ dΠand₁≤n)

mix-lift-right-OrR1 {Γ} {Δ} {Γ'} {Δ'} {A} {B} {C} {α} {β} n (Π₀ , dΠ₀≤n) =
  Π₃ , dΠ₃≤n
  where
    lhs : Ctx
    lhs = Γ ++ (Γ' -pf (A ^ α))

    rhsB : Ctx
    rhsB = (Δ -pf (A ^ α)) ++ ((B ^ β) ∷ Δ')

    rhsOr : Ctx
    rhsOr = (Δ -pf (A ^ α)) ++ ((Or B C ^ β) ∷ Δ')

    subD₁ : rhsB ⊆ ((B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    subD₁ = subset-append-mid-cons (Δ -pf (A ^ α)) Δ' (B ^ β)

    Π₁ : lhs ⊢ ((B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    Π₁ = structural subset-refl subD₁ Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subset-refl subD₁ Π₀ dΠ₀≤n)

    Π₂ : lhs ⊢ ((Or B C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    Π₂ = OrR1 Π₁

    subD₂ : ((Or B C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ')) ⊆ rhsOr
    subD₂ = subset-cons-append-mid (Δ -pf (A ^ α)) Δ' (Or B C ^ β)

    Π₃ : lhs ⊢ rhsOr
    Π₃ = structural subset-refl subD₂ Π₂

    dΠ₃≤n : δ Π₃ ≤ n
    dΠ₃≤n =
      snd (structural-δ subset-refl subD₂ Π₂ dΠ₁≤n)

mix-lift-right-OrR2 {Γ} {Δ} {Γ'} {Δ'} {A} {B} {C} {α} {β} n (Π₀ , dΠ₀≤n) =
  Π₃ , dΠ₃≤n
  where
    lhs : Ctx
    lhs = Γ ++ (Γ' -pf (A ^ α))

    rhsC : Ctx
    rhsC = (Δ -pf (A ^ α)) ++ ((C ^ β) ∷ Δ')

    rhsOr : Ctx
    rhsOr = (Δ -pf (A ^ α)) ++ ((Or B C ^ β) ∷ Δ')

    subD₁ : rhsC ⊆ ((C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    subD₁ = subset-append-mid-cons (Δ -pf (A ^ α)) Δ' (C ^ β)

    Π₁ : lhs ⊢ ((C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    Π₁ = structural subset-refl subD₁ Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subset-refl subD₁ Π₀ dΠ₀≤n)

    Π₂ : lhs ⊢ ((Or B C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    Π₂ = OrR2 Π₁

    subD₂ : ((Or B C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ')) ⊆ rhsOr
    subD₂ = subset-cons-append-mid (Δ -pf (A ^ α)) Δ' (Or B C ^ β)

    Π₃ : lhs ⊢ rhsOr
    Π₃ = structural subset-refl subD₂ Π₂

    dΠ₃≤n : δ Π₃ ≤ n
    dΠ₃≤n =
      snd (structural-δ subset-refl subD₂ Π₂ dΠ₁≤n)

mix-lift-right-ImpR {Γ} {Δ} {Γ'} {Δ'} {A} {B} {C} {α} {β} imp≢a n (Π₀ , dΠ₀≤n) =
  bCase ((B ^ β) ≟pf (A ^ α))
  where
    lhs : Ctx
    lhs = Γ ++ (Γ' -pf (A ^ α))

    lhsPrem : Ctx
    lhsPrem = (B ^ β) ∷ lhs

    rhs₀ : Ctx
    rhs₀ = (Δ -pf (A ^ α)) ++ ((C ^ β) ∷ Δ')

    rhsPrem : Ctx
    rhsPrem = (C ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ')

    rhsImp : Ctx
    rhsImp = (Δ -pf (A ^ α)) ++ (((B ⇒ C) ^ β) ∷ Δ')

    subD₁ : rhs₀ ⊆ rhsPrem
    subD₁ = subset-append-mid-cons (Δ -pf (A ^ α)) Δ' (C ^ β)

    bCase : Dec ((B ^ β) ≡ (A ^ α))
      → Σ (lhs ⊢ rhsImp) (λ Π₀ → δ Π₀ ≤ n)

    bCase (yes eqBA) =
      Πres , dΠres≤n
      where
        eqAnt : (((B ^ β) ∷ Γ') -pf (A ^ α))
             ≡ (Γ' -pf (A ^ α))
        eqAnt = pf-cons-eq {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'} eqBA

        eqAntCtx : (Γ ++ (((B ^ β) ∷ Γ') -pf (A ^ α))) ≡ lhs
        eqAntCtx = cong (Γ ++_) eqAnt

        Πbase : lhs ⊢ rhs₀
        Πbase = subst (λ xs → xs ⊢ rhs₀) eqAntCtx Π₀

        dΠbase≤n : δ Πbase ≤ n
        dΠbase≤n =
          snd (subst-δ-Γ eqAntCtx Π₀ dΠ₀≤n)

        ΠL : lhsPrem ⊢ rhs₀
        ΠL = WeakenL Πbase

        Πprem : lhsPrem ⊢ rhsPrem
        Πprem = structural subset-refl subD₁ ΠL

        dΠprem≤n : δ Πprem ≤ n
        dΠprem≤n =
          snd (structural-δ subset-refl subD₁ ΠL dΠbase≤n)

        Πimp : lhs ⊢ (((B ⇒ C) ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πimp = ImpR Πprem

        subD₂ : (((B ⇒ C) ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ')) ⊆ rhsImp
        subD₂ = subset-cons-append-mid (Δ -pf (A ^ α)) Δ' ((B ⇒ C) ^ β)

        Πres : lhs ⊢ rhsImp
        Πres = structural subset-refl subD₂ Πimp

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (structural-δ subset-refl subD₂ Πimp dΠprem≤n)

    bCase (no b≢a) =
      Πres , dΠres≤n
      where
        rem : Ctx
        rem = Γ' -pf (A ^ α)

        eqAnt : (((B ^ β) ∷ Γ') -pf (A ^ α))
             ≡ ((B ^ β) ∷ rem)
        eqAnt =
          pf-cons-neq
            {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'}
            (λ q → b≢a (sym q))

        eqAntCtx : (Γ ++ (((B ^ β) ∷ Γ') -pf (A ^ α)))
               ≡ (Γ ++ ((B ^ β) ∷ rem))
        eqAntCtx = cong (Γ ++_) eqAnt

        Πmid₀ : (Γ ++ ((B ^ β) ∷ rem)) ⊢ rhs₀
        Πmid₀ = subst (λ xs → xs ⊢ rhs₀) eqAntCtx Π₀

        dΠmid₀≤n : δ Πmid₀ ≤ n
        dΠmid₀≤n =
          snd (subst-δ-Γ eqAntCtx Π₀ dΠ₀≤n)

        subL : (Γ ++ ((B ^ β) ∷ rem)) ⊆ lhsPrem
        subL = subset-append-mid-cons Γ rem (B ^ β)

        ΠL : lhsPrem ⊢ rhs₀
        ΠL = structural subL subset-refl Πmid₀

        dΠL≤n : δ ΠL ≤ n
        dΠL≤n =
          snd (structural-δ subL subset-refl Πmid₀ dΠmid₀≤n)

        Πprem : lhsPrem ⊢ rhsPrem
        Πprem = structural subset-refl subD₁ ΠL

        dΠprem≤n : δ Πprem ≤ n
        dΠprem≤n =
          snd (structural-δ subset-refl subD₁ ΠL dΠL≤n)

        Πimp : lhs ⊢ (((B ⇒ C) ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        Πimp = ImpR Πprem

        subD₂ : (((B ⇒ C) ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ')) ⊆ rhsImp
        subD₂ = subset-cons-append-mid (Δ -pf (A ^ α)) Δ' ((B ⇒ C) ^ β)

        Πres : lhs ⊢ rhsImp
        Πres = structural subset-refl subD₂ Πimp

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (structural-δ subset-refl subD₂ Πimp dΠprem≤n)

mix-lift-right-NotR {Γ} {Δ} {Γ'} {Δ'} {A} {B} {α} {β} not≢a n (Π₀ , dΠ₀≤n) =
  bCase ((B ^ β) ≟pf (A ^ α))
  where
    lhs : Ctx
    lhs = Γ ++ (Γ' -pf (A ^ α))

    lhsWithB : Ctx
    lhsWithB = Γ ++ (((B ^ β) ∷ Γ') -pf (A ^ α))

    rhs : Ctx
    rhs = (Δ -pf (A ^ α)) ++ Δ'

    bCase : Dec ((B ^ β) ≡ (A ^ α))
      → Σ (lhs ⊢ ((Δ -pf (A ^ α)) ++ ((Not B ^ β) ∷ Δ')))
          (λ Π₀ → δ Π₀ ≤ n)

    bCase (yes eqBA) =
      Πres , dΠres≤n
      where
        eqAnt : (((B ^ β) ∷ Γ') -pf (A ^ α))
             ≡ (Γ' -pf (A ^ α))
        eqAnt = pf-cons-eq {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'} eqBA

        eqAntCtx : lhsWithB ≡ lhs
        eqAntCtx = cong (Γ ++_) eqAnt

        Πbase : lhs ⊢ rhs
        Πbase = subst (λ xs → xs ⊢ rhs) eqAntCtx Π₀

        dΠbase≤n : δ Πbase ≤ n
        dΠbase≤n =
          snd (subst-δ-Γ eqAntCtx Π₀ dΠ₀≤n)

        Πprem : ((B ^ β) ∷ lhs) ⊢ rhs
        Πprem = WeakenL Πbase

        Πnot : lhs ⊢ ((Not B ^ β) ∷ rhs)
        Πnot = NotR Πprem

        subD : ((Not B ^ β) ∷ rhs) ⊆ ((Δ -pf (A ^ α)) ++ ((Not B ^ β) ∷ Δ'))
        subD = subset-cons-append-mid (Δ -pf (A ^ α)) Δ' (Not B ^ β)

        Πres : lhs ⊢ ((Δ -pf (A ^ α)) ++ ((Not B ^ β) ∷ Δ'))
        Πres = structural subset-refl subD Πnot

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (structural-δ subset-refl subD Πnot dΠbase≤n)

    bCase (no b≢a) =
      Πres , dΠres≤n
      where
        eqAnt : (((B ^ β) ∷ Γ') -pf (A ^ α))
             ≡ ((B ^ β) ∷ (Γ' -pf (A ^ α)))
        eqAnt =
          pf-cons-neq
            {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'}
            (λ q → b≢a (sym q))

        eqAntCtx : lhsWithB ≡ (Γ ++ ((B ^ β) ∷ (Γ' -pf (A ^ α))))
        eqAntCtx = cong (Γ ++_) eqAnt

        Πmid₀ : (Γ ++ ((B ^ β) ∷ (Γ' -pf (A ^ α)))) ⊢ rhs
        Πmid₀ = subst (λ xs → xs ⊢ rhs) eqAntCtx Π₀

        dΠmid₀≤n : δ Πmid₀ ≤ n
        dΠmid₀≤n =
          snd (subst-δ-Γ eqAntCtx Π₀ dΠ₀≤n)

        subL : (Γ ++ ((B ^ β) ∷ (Γ' -pf (A ^ α))))
            ⊆ ((B ^ β) ∷ (Γ ++ (Γ' -pf (A ^ α))))
        subL = subset-append-mid-cons Γ (Γ' -pf (A ^ α)) (B ^ β)

        Πprem : ((B ^ β) ∷ lhs) ⊢ rhs
        Πprem = structural subL subset-refl Πmid₀

        dΠprem≤n : δ Πprem ≤ n
        dΠprem≤n =
          snd (structural-δ subL subset-refl Πmid₀ dΠmid₀≤n)

        Πnot : lhs ⊢ ((Not B ^ β) ∷ rhs)
        Πnot = NotR Πprem

        subD : ((Not B ^ β) ∷ rhs) ⊆ ((Δ -pf (A ^ α)) ++ ((Not B ^ β) ∷ Δ'))
        subD = subset-cons-append-mid (Δ -pf (A ^ α)) Δ' (Not B ^ β)

        Πres : lhs ⊢ ((Δ -pf (A ^ α)) ++ ((Not B ^ β) ∷ Δ'))
        Πres = structural subset-refl subD Πnot

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (structural-δ subset-refl subD Πnot dΠprem≤n)

mix-lift-right-WeakenR {Γ} {Δ} {Γ'} {Δ'} {A} {C} {α} {γ} n (Π₀ , dΠ₀≤n) =
  Π₂ , dΠ₂≤n
  where
    Π₁ : (Γ ++ (Γ' -pf (A ^ α)))
       ⊢ ((C ^ γ) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    Π₁ = WeakenR Π₀

    subD : ((C ^ γ) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        ⊆ ((Δ -pf (A ^ α)) ++ ((C ^ γ) ∷ Δ'))
    subD = subset-cons-append-mid (Δ -pf (A ^ α)) Δ' (C ^ γ)

    Π₂ : (Γ ++ (Γ' -pf (A ^ α)))
       ⊢ ((Δ -pf (A ^ α)) ++ ((C ^ γ) ∷ Δ'))
    Π₂ = structural subset-refl subD Π₁

    dΠ₂≤n : δ Π₂ ≤ n
    dΠ₂≤n =
      snd (structural-δ subset-refl subD Π₁ dΠ₀≤n)

mix-lift-left-WeakenR {Γ} {Δ} {Γ'} {Δ'} {A} {C} {α} {γ} n (Π₀ , dΠ₀≤n) =
  Π₁ , dΠ₁≤n
  where
    subD : ((Δ -pf (A ^ α)) ++ Δ') ⊆ ((((C ^ γ) ∷ Δ) -pf (A ^ α)) ++ Δ')
    subD = solveCtx⊆!

    Π₁ : (Γ ++ (Γ' -pf (A ^ α)))
       ⊢ ((((C ^ γ) ∷ Δ) -pf (A ^ α)) ++ Δ')
    Π₁ = structural subset-refl subD Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subset-refl subD Π₀ dΠ₀≤n)

mix-lift-right-WeakenL {Γ} {Δ} {Γ'} {Δ'} {A} {C} {α} {γ} n (Π₀ , dΠ₀≤n) =
  Π₁ , dΠ₁≤n
  where
    subL : (Γ ++ (Γ' -pf (A ^ α))) ⊆ (Γ ++ (((C ^ γ) ∷ Γ') -pf (A ^ α)))
    subL = solveCtx⊆!

    Π₁ : (Γ ++ (((C ^ γ) ∷ Γ') -pf (A ^ α))) ⊢ ((Δ -pf (A ^ α)) ++ Δ')
    Π₁ = structural subL subset-refl Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subL subset-refl Π₀ dΠ₀≤n)

mix-lift-right-ContractL {Γ} {Δ} {Γ'} {Δ'} {A} {C} {α} {γ} n (Π₀ , dΠ₀≤n) =
  Π₁ , dΠ₁≤n
  where
    subL : (Γ ++ (((C ^ γ) ∷ (C ^ γ) ∷ Γ') -pf (A ^ α)))
       ⊆ (Γ ++ (((C ^ γ) ∷ Γ') -pf (A ^ α)))
    subL = solveCtx⊆!

    Π₁ : (Γ ++ (((C ^ γ) ∷ Γ') -pf (A ^ α))) ⊢ ((Δ -pf (A ^ α)) ++ Δ')
    Π₁ = structural subL subset-refl Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subL subset-refl Π₀ dΠ₀≤n)

mix-lift-right-ContractR {Γ} {Δ} {Γ'} {Δ'} {A} {C} {α} {γ} n (Π₀ , dΠ₀≤n) =
  Π₁ , dΠ₁≤n
  where
    subD : ((Δ -pf (A ^ α)) ++ ((C ^ γ) ∷ (C ^ γ) ∷ Δ'))
        ⊆ ((Δ -pf (A ^ α)) ++ ((C ^ γ) ∷ Δ'))
    subD = subset-drop-dup-mid (Δ -pf (A ^ α)) Δ' (C ^ γ)

    Π₁ : (Γ ++ (Γ' -pf (A ^ α)))
       ⊢ ((Δ -pf (A ^ α)) ++ ((C ^ γ) ∷ Δ'))
    Π₁ = structural subset-refl subD Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subset-refl subD Π₀ dΠ₀≤n)

mix-lift-left-ExchangeL
  {Γ₁} {Γ₂} {Δ} {Γ'} {Δ'} {A} {α} {c} {d} n (Π₀ , dΠ₀≤n) =
  Π₁ , dΠ₁≤n
  where
    subL : ((Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂) ++ (Γ' -pf (A ^ α)))
       ⊆ (((Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂) ++ (Γ' -pf (A ^ α))))
    subL = solveCtx⊆!

    Π₁ : ((Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂) ++ (Γ' -pf (A ^ α)))
       ⊢ ((Δ -pf (A ^ α)) ++ Δ')
    Π₁ = structural subL subset-refl Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subL subset-refl Π₀ dΠ₀≤n)

mix-lift-right-ExchangeR
  {Γ} {Δ₁} {Δ₂} {Γ'} {Δ} {A} {α} {c} {d} n (Π₀ , dΠ₀≤n) =
  Π₁ , dΠ₁≤n
  where
    subD : ((Δ -pf (A ^ α)) ++ (Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂))
       ⊆ (((Δ -pf (A ^ α)) ++ (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂)))
    subD = solveCtx⊆!

    Π₁ : (Γ ++ (Γ' -pf (A ^ α))) ⊢ ((Δ -pf (A ^ α)) ++ (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂))
    Π₁ = structural subset-refl subD Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subset-refl subD Π₀ dΠ₀≤n)

mix-lift-left-ExchangeR
  {Γ} {Δ₁} {Δ₂} {Γ'} {Δ'} {A} {α} {c} {d} n (Π₀ , dΠ₀≤n) =
  Π₁ , dΠ₁≤n
  where
    subD : ((((Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂) -pf (A ^ α)) ++ Δ'))
        ⊆ (((((Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂) -pf (A ^ α)) ++ Δ')))
    subD = solveCtx⊆!

    Π₁ : (Γ ++ (Γ' -pf (A ^ α))) ⊢ ((((Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂) -pf (A ^ α)) ++ Δ'))
    Π₁ = structural subset-refl subD Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subset-refl subD Π₀ dΠ₀≤n)

mix-lift-right-ExchangeL
  {Γ} {Δ} {Γ₁} {Γ₂} {Δ'} {A} {α} {c} {d} n (Π₀ , dΠ₀≤n) =
  Π₁ , dΠ₁≤n
  where
    subL : (Γ ++ ((Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂) -pf (A ^ α)))
       ⊆ (Γ ++ ((Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂) -pf (A ^ α)))
    subL = solveCtx⊆!

    Π₁ : (Γ ++ ((Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂) -pf (A ^ α))) ⊢ ((Δ -pf (A ^ α)) ++ Δ')
    Π₁ = structural subL subset-refl Π₀

    dΠ₁≤n : δ Π₁ ≤ n
    dΠ₁≤n =
      snd (structural-δ subL subset-refl Π₀ dΠ₀≤n)

mix-lift-right-AndR :
  ∀ {Γ Δ Γ₁' Γ₂' Δ₁' Δ₂'} {A B C : Formula} {α β : Position}
  → (n : ℕ)
  → Σ ((Γ ++ (Γ₁' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ (B ^ β) ∷ Δ₁'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ₂' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ (C ^ β) ∷ Δ₂'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ ((Γ₁' ++ Γ₂') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ (And B C ^ β) ∷ (Δ₁' ++ Δ₂')))
      (λ Π₀ → δ Π₀ ≤ n)
mix-lift-right-AndR
  {Γ} {Δ} {Γ₁'} {Γ₂'} {Δ₁'} {Δ₂'} {A} {B} {C} {α} {β}
  n (Π₁ , dΠ₁≤n) (Π₂ , dΠ₂≤n) =
  Πres , dΠres≤n
  where
    rem : Ctx
    rem = Δ -pf (A ^ α)

    subD₁ : (rem ++ (B ^ β) ∷ Δ₁') ⊆ ((B ^ β) ∷ (rem ++ Δ₁'))
    subD₁ = subset-append-mid-cons rem Δ₁' (B ^ β)

    Πb : (Γ ++ (Γ₁' -pf (A ^ α))) ⊢ ((B ^ β) ∷ (rem ++ Δ₁'))
    Πb = structural subset-refl subD₁ Π₁

    dΠb≤n : δ Πb ≤ n
    dΠb≤n =
      snd (structural-δ subset-refl subD₁ Π₁ dΠ₁≤n)

    subD₂ : (rem ++ (C ^ β) ∷ Δ₂') ⊆ ((C ^ β) ∷ (rem ++ Δ₂'))
    subD₂ = subset-append-mid-cons rem Δ₂' (C ^ β)

    Πc : (Γ ++ (Γ₂' -pf (A ^ α))) ⊢ ((C ^ β) ∷ (rem ++ Δ₂'))
    Πc = structural subset-refl subD₂ Π₂

    dΠc≤n : δ Πc ≤ n
    dΠc≤n =
      snd (structural-δ subset-refl subD₂ Π₂ dΠ₂≤n)

    Πand₀ : ((Γ ++ (Γ₁' -pf (A ^ α))) ++ (Γ ++ (Γ₂' -pf (A ^ α))))
          ⊢ ((And B C ^ β) ∷ ((rem ++ Δ₁') ++ (rem ++ Δ₂')))
    Πand₀ = AndR Πb Πc

    dΠand₀≤n : δ Πand₀ ≤ n
    dΠand₀≤n = max-least dΠb≤n dΠc≤n

    lhsExpanded : Ctx
    lhsExpanded = Γ ++ ((Γ₁' -pf (A ^ α)) ++ (Γ₂' -pf (A ^ α)))

    rhsMid : Ctx
    rhsMid = rem ++ (And B C ^ β) ∷ (Δ₁' ++ Δ₂')

    subLFromLeft : ∀ {y : PFormula}
      → y ∈ (Γ ++ (Γ₁' -pf (A ^ α)))
      → y ∈ lhsExpanded
    subLFromLeft {y} yInL with ∈-++⁻ Γ {ys = Γ₁' -pf (A ^ α)} yInL
    ... | inl yInΓ = ∈-++⁺ˡ yInΓ
    ... | inr yInΓ₁ = ∈-++⁺ʳ Γ (∈-++⁺ˡ yInΓ₁)

    subLFromRight : ∀ {y : PFormula}
      → y ∈ (Γ ++ (Γ₂' -pf (A ^ α)))
      → y ∈ lhsExpanded
    subLFromRight {y} yInR with ∈-++⁻ Γ {ys = Γ₂' -pf (A ^ α)} yInR
    ... | inl yInΓ = ∈-++⁺ˡ yInΓ
    ... | inr yInΓ₂ = ∈-++⁺ʳ Γ (∈-++⁺ʳ (Γ₁' -pf (A ^ α)) yInΓ₂)

    subL : ((Γ ++ (Γ₁' -pf (A ^ α))) ++ (Γ ++ (Γ₂' -pf (A ^ α))))
       ⊆ lhsExpanded
    subL {y} yIn with ∈-++⁻ (Γ ++ (Γ₁' -pf (A ^ α))) {ys = Γ ++ (Γ₂' -pf (A ^ α))} yIn
    ... | inl yInL = subLFromLeft yInL
    ... | inr yInR = subLFromRight yInR

    tailDstExpanded : Ctx
    tailDstExpanded = rem ++ (Δ₁' ++ Δ₂')

    tailSubFromLeft : ∀ {y : PFormula}
      → y ∈ (rem ++ Δ₁')
      → y ∈ tailDstExpanded
    tailSubFromLeft {y} yInL with ∈-++⁻ rem {ys = Δ₁'} yInL
    ... | inl yInRem = ∈-++⁺ˡ yInRem
    ... | inr yInΔ₁ = ∈-++⁺ʳ rem (∈-++⁺ˡ yInΔ₁)

    tailSubFromRight : ∀ {y : PFormula}
      → y ∈ (rem ++ Δ₂')
      → y ∈ tailDstExpanded
    tailSubFromRight {y} yInR with ∈-++⁻ rem {ys = Δ₂'} yInR
    ... | inl yInRem = ∈-++⁺ˡ yInRem
    ... | inr yInΔ₂ = ∈-++⁺ʳ rem (∈-++⁺ʳ Δ₁' yInΔ₂)

    tailSub : ((rem ++ Δ₁') ++ (rem ++ Δ₂')) ⊆ tailDstExpanded
    tailSub {y} yIn with ∈-++⁻ (rem ++ Δ₁') {ys = rem ++ Δ₂'} yIn
    ... | inl yInL = tailSubFromLeft yInL
    ... | inr yInR = tailSubFromRight yInR

    subD : ((And B C ^ β) ∷ ((rem ++ Δ₁') ++ (rem ++ Δ₂'))) ⊆ rhsMid
    subD {y} yIn with yIn
    ... | here y≡And = ∈-++⁺ʳ rem (here y≡And)
    ... | there yInTail with ∈-++⁻ rem {ys = Δ₁' ++ Δ₂'} (tailSub yInTail)
    ...   | inl yInRem = ∈-++⁺ˡ yInRem
    ...   | inr yInΔ = ∈-++⁺ʳ rem (there yInΔ)

    Πmid : lhsExpanded ⊢ rhsMid
    Πmid = structural subL subD Πand₀

    dΠmid≤n : δ Πmid ≤ n
    dΠmid≤n =
      snd (structural-δ subL subD Πand₀ dΠand₀≤n)

    lhsEq : lhsExpanded ≡ (Γ ++ ((Γ₁' ++ Γ₂') -pf (A ^ α)))
    lhsEq = cong (Γ ++_) (sym (pf-++ (A ^ α) Γ₁' Γ₂'))

    Πres : (Γ ++ ((Γ₁' ++ Γ₂') -pf (A ^ α)))
       ⊢ ((Δ -pf (A ^ α)) ++ (And B C ^ β) ∷ (Δ₁' ++ Δ₂'))
    Πres = subst (λ xs → xs ⊢ rhsMid) lhsEq Πmid

    dΠres≤n : δ Πres ≤ n
    dΠres≤n =
      snd (subst-δ-Γ lhsEq Πmid dΠmid≤n)

mix-lift-right-OrL :
  ∀ {Γ Δ Γ₁' Γ₂' Δ₁' Δ₂'} {A B C : Formula} {α β : Position}
  → Neg ((Or B C ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((Γ ++ (((B ^ β) ∷ Γ₁') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ₁'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (((C ^ β) ∷ Γ₂') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ₂'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (((Or B C ^ β) ∷ (Γ₁' ++ Γ₂')) -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ (Δ₁' ++ Δ₂')))
      (λ Π₀ → δ Π₀ ≤ n)
mix-lift-right-OrL
  {Γ} {Δ} {Γ₁'} {Γ₂'} {Δ₁'} {Δ₂'} {A} {B} {C} {α} {β}
  or≢a n (Π₁ , dΠ₁≤n) (Π₂ , dΠ₂≤n) =
  Πres , dΠres≤n
  where
    remΔ : Ctx
    remΔ = Δ -pf (A ^ α)

    remL : Ctx
    remL = Γ₁' -pf (A ^ α)

    remR : Ctx
    remR = Γ₂' -pf (A ^ α)

    rhs₁ : Ctx
    rhs₁ = remΔ ++ Δ₁'

    rhs₂ : Ctx
    rhs₂ = remΔ ++ Δ₂'

    ΠbPrem :
      Σ (((B ^ β) ∷ (Γ ++ remL)) ⊢ rhs₁)
        (λ Π₀ → δ Π₀ ≤ n)
    ΠbPrem = bCase ((B ^ β) ≟pf (A ^ α))
      where
        bCase : Dec ((B ^ β) ≡ (A ^ α))
          → Σ (((B ^ β) ∷ (Γ ++ remL)) ⊢ rhs₁)
              (λ Π₀ → δ Π₀ ≤ n)
        bCase (yes eqBA) =
          Πprem , dΠbase≤n
          where
            eqAnt : (((B ^ β) ∷ Γ₁') -pf (A ^ α))
                 ≡ remL
            eqAnt = pf-cons-eq {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ₁'} eqBA

            eqCtx : (Γ ++ (((B ^ β) ∷ Γ₁') -pf (A ^ α)))
                ≡ (Γ ++ remL)
            eqCtx = cong (Γ ++_) eqAnt

            Πbase : (Γ ++ remL) ⊢ rhs₁
            Πbase = subst (λ xs → xs ⊢ rhs₁) eqCtx Π₁

            dΠbase≤n : δ Πbase ≤ n
            dΠbase≤n =
              snd (subst-δ-Γ eqCtx Π₁ dΠ₁≤n)

            Πprem : ((B ^ β) ∷ (Γ ++ remL)) ⊢ rhs₁
            Πprem = WeakenL Πbase

        bCase (no b≢a) =
          Πprem , dΠprem≤n
          where
            eqAnt : (((B ^ β) ∷ Γ₁') -pf (A ^ α))
                 ≡ ((B ^ β) ∷ remL)
            eqAnt =
              pf-cons-neq
                {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ₁'}
                (λ q → b≢a (sym q))

            eqCtx : (Γ ++ (((B ^ β) ∷ Γ₁') -pf (A ^ α)))
                ≡ (Γ ++ ((B ^ β) ∷ remL))
            eqCtx = cong (Γ ++_) eqAnt

            Πmid₀ : (Γ ++ ((B ^ β) ∷ remL)) ⊢ rhs₁
            Πmid₀ = subst (λ xs → xs ⊢ rhs₁) eqCtx Π₁

            dΠmid₀≤n : δ Πmid₀ ≤ n
            dΠmid₀≤n =
              snd (subst-δ-Γ eqCtx Π₁ dΠ₁≤n)

            subL : (Γ ++ ((B ^ β) ∷ remL))
                ⊆ ((B ^ β) ∷ (Γ ++ remL))
            subL = subset-append-mid-cons Γ remL (B ^ β)

            Πprem : ((B ^ β) ∷ (Γ ++ remL)) ⊢ rhs₁
            Πprem = structural subL subset-refl Πmid₀

            dΠprem≤n : δ Πprem ≤ n
            dΠprem≤n =
              snd (structural-δ subL subset-refl Πmid₀ dΠmid₀≤n)

    ΠcPrem :
      Σ (((C ^ β) ∷ (Γ ++ remR)) ⊢ rhs₂)
        (λ Π₀ → δ Π₀ ≤ n)
    ΠcPrem = cCase ((C ^ β) ≟pf (A ^ α))
      where
        cCase : Dec ((C ^ β) ≡ (A ^ α))
          → Σ (((C ^ β) ∷ (Γ ++ remR)) ⊢ rhs₂)
              (λ Π₀ → δ Π₀ ≤ n)
        cCase (yes eqCA) =
          Πprem , dΠbase≤n
          where
            eqAnt : (((C ^ β) ∷ Γ₂') -pf (A ^ α))
                 ≡ remR
            eqAnt = pf-cons-eq {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Γ₂'} eqCA

            eqCtx : (Γ ++ (((C ^ β) ∷ Γ₂') -pf (A ^ α)))
                ≡ (Γ ++ remR)
            eqCtx = cong (Γ ++_) eqAnt

            Πbase : (Γ ++ remR) ⊢ rhs₂
            Πbase = subst (λ xs → xs ⊢ rhs₂) eqCtx Π₂

            dΠbase≤n : δ Πbase ≤ n
            dΠbase≤n =
              snd (subst-δ-Γ eqCtx Π₂ dΠ₂≤n)

            Πprem : ((C ^ β) ∷ (Γ ++ remR)) ⊢ rhs₂
            Πprem = WeakenL Πbase

        cCase (no c≢a) =
          Πprem , dΠprem≤n
          where
            eqAnt : (((C ^ β) ∷ Γ₂') -pf (A ^ α))
                 ≡ ((C ^ β) ∷ remR)
            eqAnt =
              pf-cons-neq
                {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Γ₂'}
                (λ q → c≢a (sym q))

            eqCtx : (Γ ++ (((C ^ β) ∷ Γ₂') -pf (A ^ α)))
                ≡ (Γ ++ ((C ^ β) ∷ remR))
            eqCtx = cong (Γ ++_) eqAnt

            Πmid₀ : (Γ ++ ((C ^ β) ∷ remR)) ⊢ rhs₂
            Πmid₀ = subst (λ xs → xs ⊢ rhs₂) eqCtx Π₂

            dΠmid₀≤n : δ Πmid₀ ≤ n
            dΠmid₀≤n =
              snd (subst-δ-Γ eqCtx Π₂ dΠ₂≤n)

            subL : (Γ ++ ((C ^ β) ∷ remR))
                ⊆ ((C ^ β) ∷ (Γ ++ remR))
            subL = subset-append-mid-cons Γ remR (C ^ β)

            Πprem : ((C ^ β) ∷ (Γ ++ remR)) ⊢ rhs₂
            Πprem = structural subL subset-refl Πmid₀

            dΠprem≤n : δ Πprem ≤ n
            dΠprem≤n =
              snd (structural-δ subL subset-refl Πmid₀ dΠmid₀≤n)

    Πb : ((B ^ β) ∷ (Γ ++ remL)) ⊢ rhs₁
    Πb = fst ΠbPrem

    dΠb≤n : δ Πb ≤ n
    dΠb≤n = snd ΠbPrem

    Πc : ((C ^ β) ∷ (Γ ++ remR)) ⊢ rhs₂
    Πc = fst ΠcPrem

    dΠc≤n : δ Πc ≤ n
    dΠc≤n = snd ΠcPrem

    Πor₀ : ((Or B C ^ β) ∷ ((Γ ++ remL) ++ (Γ ++ remR)))
         ⊢ (rhs₁ ++ rhs₂)
    Πor₀ = OrL Πb Πc

    dΠor₀≤n : δ Πor₀ ≤ n
    dΠor₀≤n = max-least dΠb≤n dΠc≤n

    lhsTargetExpanded : Ctx
    lhsTargetExpanded = Γ ++ ((Or B C ^ β) ∷ (remL ++ remR))

    rhsTarget : Ctx
    rhsTarget = remΔ ++ (Δ₁' ++ Δ₂')

    subLFromLeft : ∀ {y : PFormula}
      → y ∈ (Γ ++ remL)
      → y ∈ lhsTargetExpanded
    subLFromLeft {y} yInL with ∈-++⁻ Γ {ys = remL} yInL
    ... | inl yInΓ = ∈-++⁺ˡ yInΓ
    ... | inr yInRemL = ∈-++⁺ʳ Γ (there (∈-++⁺ˡ yInRemL))

    subLFromRight : ∀ {y : PFormula}
      → y ∈ (Γ ++ remR)
      → y ∈ lhsTargetExpanded
    subLFromRight {y} yInR with ∈-++⁻ Γ {ys = remR} yInR
    ... | inl yInΓ = ∈-++⁺ˡ yInΓ
    ... | inr yInRemR = ∈-++⁺ʳ Γ (there (∈-++⁺ʳ remL yInRemR))

    subL : ((Or B C ^ β) ∷ ((Γ ++ remL) ++ (Γ ++ remR))) ⊆ lhsTargetExpanded
    subL {y} yIn with yIn
    ... | here y≡or = ∈-++⁺ʳ Γ (here y≡or)
    ... | there yInTail with ∈-++⁻ (Γ ++ remL) {ys = Γ ++ remR} yInTail
    ... | inl yInLeft = subLFromLeft yInLeft
    ... | inr yInRight = subLFromRight yInRight

    subDFromLeft : ∀ {y : PFormula}
      → y ∈ rhs₁
      → y ∈ rhsTarget
    subDFromLeft {y} yInL with ∈-++⁻ remΔ {ys = Δ₁'} yInL
    ... | inl yInRem = ∈-++⁺ˡ yInRem
    ... | inr yInΔ₁ = ∈-++⁺ʳ remΔ (∈-++⁺ˡ yInΔ₁)

    subDFromRight : ∀ {y : PFormula}
      → y ∈ rhs₂
      → y ∈ rhsTarget
    subDFromRight {y} yInR with ∈-++⁻ remΔ {ys = Δ₂'} yInR
    ... | inl yInRem = ∈-++⁺ˡ yInRem
    ... | inr yInΔ₂ = ∈-++⁺ʳ remΔ (∈-++⁺ʳ Δ₁' yInΔ₂)

    subD : (rhs₁ ++ rhs₂) ⊆ rhsTarget
    subD {y} yIn with ∈-++⁻ rhs₁ {ys = rhs₂} yIn
    ... | inl yInL = subDFromLeft yInL
    ... | inr yInR = subDFromRight yInR

    Πmid : lhsTargetExpanded ⊢ rhsTarget
    Πmid = structural subL subD Πor₀

    dΠmid≤n : δ Πmid ≤ n
    dΠmid≤n =
      snd (structural-δ subL subD Πor₀ dΠor₀≤n)

    eqOrRem : (((Or B C ^ β) ∷ (Γ₁' ++ Γ₂')) -pf (A ^ α))
           ≡ ((Or B C ^ β) ∷ (remL ++ remR))
    eqOrRem =
      pf-cons-neq
        {φ = (A ^ α)} {ψ = (Or B C ^ β)} {Γ = (Γ₁' ++ Γ₂')}
        (λ q → or≢a (sym q))
      ∙ cong ((Or B C ^ β) ∷_) (pf-++ (A ^ α) Γ₁' Γ₂')

    eqCtx : lhsTargetExpanded
        ≡ (Γ ++ (((Or B C ^ β) ∷ (Γ₁' ++ Γ₂')) -pf (A ^ α)))
    eqCtx = cong (Γ ++_) (sym eqOrRem)

    Πres : (Γ ++ (((Or B C ^ β) ∷ (Γ₁' ++ Γ₂')) -pf (A ^ α)))
       ⊢ ((Δ -pf (A ^ α)) ++ (Δ₁' ++ Δ₂'))
    Πres = subst (λ xs → xs ⊢ rhsTarget) eqCtx Πmid

    dΠres≤n : δ Πres ≤ n
    dΠres≤n =
      snd (subst-δ-Γ eqCtx Πmid dΠmid≤n)

mix-lift-right-ImpL :
  ∀ {Γ Δ Γ₁' Γ₂' Δ₁' Δ₂'} {A B C : Formula} {α β : Position}
  → Neg (((B ⇒ C) ^ β) ≡ (A ^ α))
  → (n : ℕ)
  → Σ ((Γ ++ (Γ₁' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ (B ^ β) ∷ Δ₁'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (((C ^ β) ∷ Γ₂') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ₂'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ ((((B ⇒ C) ^ β) ∷ (Γ₁' ++ Γ₂')) -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ (Δ₁' ++ Δ₂')))
      (λ Π₀ → δ Π₀ ≤ n)
mix-lift-right-ImpL
  {Γ} {Δ} {Γ₁'} {Γ₂'} {Δ₁'} {Δ₂'} {A} {B} {C} {α} {β}
  imp≢a n (Π₁ , dΠ₁≤n) (Π₂ , dΠ₂≤n) =
  Πres , dΠres≤n
  where
    rem : Ctx
    rem = Δ -pf (A ^ α)

    rhsTarget : Ctx
    rhsTarget = rem ++ (Δ₁' ++ Δ₂')

    subD₁ : (rem ++ (B ^ β) ∷ Δ₁') ⊆ ((B ^ β) ∷ (rem ++ Δ₁'))
    subD₁ = subset-append-mid-cons rem Δ₁' (B ^ β)

    Πb : (Γ ++ (Γ₁' -pf (A ^ α))) ⊢ ((B ^ β) ∷ (rem ++ Δ₁'))
    Πb = structural subset-refl subD₁ Π₁

    dΠb≤n : δ Πb ≤ n
    dΠb≤n =
      snd (structural-δ subset-refl subD₁ Π₁ dΠ₁≤n)

    cPrem :
      Σ ((C ^ β) ∷ (Γ ++ (Γ₂' -pf (A ^ α))) ⊢ (rem ++ Δ₂'))
        (λ Π₀ → δ Π₀ ≤ n)
    cPrem = cCase ((C ^ β) ≟pf (A ^ α))
      where
        cCase : Dec ((C ^ β) ≡ (A ^ α))
          → Σ ((C ^ β) ∷ (Γ ++ (Γ₂' -pf (A ^ α))) ⊢ (rem ++ Δ₂'))
              (λ Π₀ → δ Π₀ ≤ n)
        cCase (yes eqCA) =
          Πprem , dΠbase≤n
          where
            eqAnt : (((C ^ β) ∷ Γ₂') -pf (A ^ α))
                 ≡ (Γ₂' -pf (A ^ α))
            eqAnt = pf-cons-eq {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Γ₂'} eqCA

            eqCtx : (Γ ++ (((C ^ β) ∷ Γ₂') -pf (A ^ α)))
                ≡ (Γ ++ (Γ₂' -pf (A ^ α)))
            eqCtx = cong (Γ ++_) eqAnt

            Πbase : (Γ ++ (Γ₂' -pf (A ^ α))) ⊢ (rem ++ Δ₂')
            Πbase = subst (λ xs → xs ⊢ (rem ++ Δ₂')) eqCtx Π₂

            dΠbase≤n : δ Πbase ≤ n
            dΠbase≤n =
              snd (subst-δ-Γ eqCtx Π₂ dΠ₂≤n)

            Πprem : (C ^ β) ∷ (Γ ++ (Γ₂' -pf (A ^ α))) ⊢ (rem ++ Δ₂')
            Πprem = WeakenL Πbase

        cCase (no c≢a) =
          Πprem , dΠprem≤n
          where
            eqAnt : (((C ^ β) ∷ Γ₂') -pf (A ^ α))
                 ≡ ((C ^ β) ∷ (Γ₂' -pf (A ^ α)))
            eqAnt =
              pf-cons-neq
                {φ = (A ^ α)} {ψ = (C ^ β)} {Γ = Γ₂'}
                (λ q → c≢a (sym q))

            eqCtx : (Γ ++ (((C ^ β) ∷ Γ₂') -pf (A ^ α)))
                ≡ (Γ ++ ((C ^ β) ∷ (Γ₂' -pf (A ^ α))))
            eqCtx = cong (Γ ++_) eqAnt

            Πmid₀ : (Γ ++ ((C ^ β) ∷ (Γ₂' -pf (A ^ α)))) ⊢ (rem ++ Δ₂')
            Πmid₀ = subst (λ xs → xs ⊢ (rem ++ Δ₂')) eqCtx Π₂

            dΠmid₀≤n : δ Πmid₀ ≤ n
            dΠmid₀≤n =
              snd (subst-δ-Γ eqCtx Π₂ dΠ₂≤n)

            subL : (Γ ++ ((C ^ β) ∷ (Γ₂' -pf (A ^ α))))
               ⊆ ((C ^ β) ∷ (Γ ++ (Γ₂' -pf (A ^ α))))
            subL = subset-append-mid-cons Γ (Γ₂' -pf (A ^ α)) (C ^ β)

            Πprem : (C ^ β) ∷ (Γ ++ (Γ₂' -pf (A ^ α))) ⊢ (rem ++ Δ₂')
            Πprem = structural subL subset-refl Πmid₀

            dΠprem≤n : δ Πprem ≤ n
            dΠprem≤n =
              snd (structural-δ subL subset-refl Πmid₀ dΠmid₀≤n)

    Πc : (C ^ β) ∷ (Γ ++ (Γ₂' -pf (A ^ α))) ⊢ (rem ++ Δ₂')
    Πc = fst cPrem

    dΠc≤n : δ Πc ≤ n
    dΠc≤n = snd cPrem

    Πimp₀ : ((B ⇒ C) ^ β) ∷ ((Γ ++ (Γ₁' -pf (A ^ α))) ++ (Γ ++ (Γ₂' -pf (A ^ α))))
         ⊢ ((rem ++ Δ₁') ++ (rem ++ Δ₂'))
    Πimp₀ = ImpL Πb Πc

    dΠimp₀≤n : δ Πimp₀ ≤ n
    dΠimp₀≤n = max-least dΠb≤n dΠc≤n

    lhsExpanded : Ctx
    lhsExpanded = Γ ++ (((B ⇒ C) ^ β) ∷ ((Γ₁' -pf (A ^ α)) ++ (Γ₂' -pf (A ^ α))))

    subLFromLeft : ∀ {y : PFormula}
      → y ∈ (Γ ++ (Γ₁' -pf (A ^ α)))
      → y ∈ lhsExpanded
    subLFromLeft {y} yInL with ∈-++⁻ Γ {ys = Γ₁' -pf (A ^ α)} yInL
    ... | inl yInΓ = ∈-++⁺ˡ yInΓ
    ... | inr yInΓ₁ = ∈-++⁺ʳ Γ (there (∈-++⁺ˡ yInΓ₁))

    subLFromRight : ∀ {y : PFormula}
      → y ∈ (Γ ++ (Γ₂' -pf (A ^ α)))
      → y ∈ lhsExpanded
    subLFromRight {y} yInR with ∈-++⁻ Γ {ys = Γ₂' -pf (A ^ α)} yInR
    ... | inl yInΓ = ∈-++⁺ˡ yInΓ
    ... | inr yInΓ₂ = ∈-++⁺ʳ Γ (there (∈-++⁺ʳ (Γ₁' -pf (A ^ α)) yInΓ₂))

    subL : ((B ⇒ C) ^ β) ∷ ((Γ ++ (Γ₁' -pf (A ^ α))) ++ (Γ ++ (Γ₂' -pf (A ^ α))))
       ⊆ lhsExpanded
    subL {y} yIn with yIn
    ... | here y≡Imp = ∈-++⁺ʳ Γ (here y≡Imp)
    ... | there yInTail with ∈-++⁻ (Γ ++ (Γ₁' -pf (A ^ α))) {ys = Γ ++ (Γ₂' -pf (A ^ α))} yInTail
    ... | inl yInL = subLFromLeft yInL
    ... | inr yInR = subLFromRight yInR

    subDFromLeft : ∀ {y : PFormula}
      → y ∈ (rem ++ Δ₁')
      → y ∈ rhsTarget
    subDFromLeft {y} yInL with ∈-++⁻ rem {ys = Δ₁'} yInL
    ... | inl yInRem = ∈-++⁺ˡ yInRem
    ... | inr yInΔ₁ = ∈-++⁺ʳ rem (∈-++⁺ˡ yInΔ₁)

    subDFromRight : ∀ {y : PFormula}
      → y ∈ (rem ++ Δ₂')
      → y ∈ rhsTarget
    subDFromRight {y} yInR with ∈-++⁻ rem {ys = Δ₂'} yInR
    ... | inl yInRem = ∈-++⁺ˡ yInRem
    ... | inr yInΔ₂ = ∈-++⁺ʳ rem (∈-++⁺ʳ Δ₁' yInΔ₂)

    subD : ((rem ++ Δ₁') ++ (rem ++ Δ₂')) ⊆ rhsTarget
    subD {y} yIn with ∈-++⁻ (rem ++ Δ₁') {ys = rem ++ Δ₂'} yIn
    ... | inl yInL = subDFromLeft yInL
    ... | inr yInR = subDFromRight yInR

    Πmid : lhsExpanded ⊢ rhsTarget
    Πmid = structural subL subD Πimp₀

    dΠmid≤n : δ Πmid ≤ n
    dΠmid≤n =
      snd (structural-δ subL subD Πimp₀ dΠimp₀≤n)

    eqImp : ((((B ⇒ C) ^ β) ∷ (Γ₁' ++ Γ₂')) -pf (A ^ α))
         ≡ ((B ⇒ C) ^ β) ∷ ((Γ₁' -pf (A ^ α)) ++ (Γ₂' -pf (A ^ α)))
    eqImp =
      pf-cons-neq
        {φ = (A ^ α)} {ψ = ((B ⇒ C) ^ β)} {Γ = Γ₁' ++ Γ₂'}
        (λ q → imp≢a (sym q))
      ∙ cong (((B ⇒ C) ^ β) ∷_) (pf-++ (A ^ α) Γ₁' Γ₂')

    eqCtx : lhsExpanded
        ≡ (Γ ++ ((((B ⇒ C) ^ β) ∷ (Γ₁' ++ Γ₂')) -pf (A ^ α)))
    eqCtx = cong (Γ ++_) (sym eqImp)

    Πres : (Γ ++ ((((B ⇒ C) ^ β) ∷ (Γ₁' ++ Γ₂')) -pf (A ^ α)))
       ⊢ ((Δ -pf (A ^ α)) ++ (Δ₁' ++ Δ₂'))
    Πres = subst (λ xs → xs ⊢ rhsTarget) eqCtx Πmid

    dΠres≤n : δ Πres ≤ n
    dΠres≤n =
      snd (subst-δ-Γ eqCtx Πmid dΠmid≤n)

mix-lift-right-Cut :
  ∀ {Γ Δ Γ₁' Γ₂' Δ₁' Δ₂'} {A A' : Formula} {α α' : Position}
  → cutConstraint M A' α'
      (Γ ++ (Γ₁' -pf (A ^ α)))
      (Γ ++ (Γ₂' -pf (A ^ α)))
      ((Δ -pf (A ^ α)) ++ Δ₁')
      ((Δ -pf (A ^ α)) ++ Δ₂')
  → (n : ℕ)
  → suc (degree A') ≤ n
  → Σ ((Γ ++ (Γ₁' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ [ (A' ^ α') ] ++ Δ₁'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ (((Γ ++ (Γ₂' -pf (A ^ α))) ++ [ (A' ^ α') ])
      ⊢ ((Δ -pf (A ^ α)) ++ Δ₂'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ ((Γ₁' ++ Γ₂') -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ (Δ₁' ++ Δ₂')))
      (λ Π₀ → δ Π₀ ≤ n)
mix-lift-right-Cut
  {Γ} {Δ} {Γ₁'} {Γ₂'} {Δ₁'} {Δ₂'} {A} {A'} {α} {α'}
  cCut' n dA'≤n (Π₁ , dΠ₁≤n) (Π₂ , dΠ₂≤n) =
  Πres , dΠres≤n
  where
    rem : Ctx
    rem = Δ -pf (A ^ α)

    rhsTarget : Ctx
    rhsTarget = rem ++ (Δ₁' ++ Δ₂')

    subD₁ : (rem ++ [ (A' ^ α') ] ++ Δ₁') ⊆ ((A' ^ α') ∷ (rem ++ Δ₁'))
    subD₁ = subset-append-mid-cons rem Δ₁' (A' ^ α')

    Πa : (Γ ++ (Γ₁' -pf (A ^ α))) ⊢ ((A' ^ α') ∷ (rem ++ Δ₁'))
    Πa = structural subset-refl subD₁ Π₁

    dΠa≤n : δ Πa ≤ n
    dΠa≤n =
      snd (structural-δ subset-refl subD₁ Π₁ dΠ₁≤n)

    Πcut₀ : ((Γ ++ (Γ₁' -pf (A ^ α))) ++ (Γ ++ (Γ₂' -pf (A ^ α))))
         ⊢ ((rem ++ Δ₁') ++ (rem ++ Δ₂'))
    Πcut₀ = Cut cCut' Πa Π₂

    dΠcut₀≤n : δ Πcut₀ ≤ n
    dΠcut₀≤n = max-least dA'≤n (max-least dΠa≤n dΠ₂≤n)

    lhsExpanded : Ctx
    lhsExpanded = Γ ++ ((Γ₁' -pf (A ^ α)) ++ (Γ₂' -pf (A ^ α)))

    subLFromLeft : ∀ {y : PFormula}
      → y ∈ (Γ ++ (Γ₁' -pf (A ^ α)))
      → y ∈ lhsExpanded
    subLFromLeft {y} yInL with ∈-++⁻ Γ {ys = Γ₁' -pf (A ^ α)} yInL
    ... | inl yInΓ = ∈-++⁺ˡ yInΓ
    ... | inr yInΓ₁ = ∈-++⁺ʳ Γ (∈-++⁺ˡ yInΓ₁)

    subLFromRight : ∀ {y : PFormula}
      → y ∈ (Γ ++ (Γ₂' -pf (A ^ α)))
      → y ∈ lhsExpanded
    subLFromRight {y} yInR with ∈-++⁻ Γ {ys = Γ₂' -pf (A ^ α)} yInR
    ... | inl yInΓ = ∈-++⁺ˡ yInΓ
    ... | inr yInΓ₂ = ∈-++⁺ʳ Γ (∈-++⁺ʳ (Γ₁' -pf (A ^ α)) yInΓ₂)

    subL : ((Γ ++ (Γ₁' -pf (A ^ α))) ++ (Γ ++ (Γ₂' -pf (A ^ α))))
       ⊆ lhsExpanded
    subL {y} yIn with ∈-++⁻ (Γ ++ (Γ₁' -pf (A ^ α))) {ys = Γ ++ (Γ₂' -pf (A ^ α))} yIn
    ... | inl yInL = subLFromLeft yInL
    ... | inr yInR = subLFromRight yInR

    subDFromLeft : ∀ {y : PFormula}
      → y ∈ (rem ++ Δ₁')
      → y ∈ rhsTarget
    subDFromLeft {y} yInL with ∈-++⁻ rem {ys = Δ₁'} yInL
    ... | inl yInRem = ∈-++⁺ˡ yInRem
    ... | inr yInΔ₁ = ∈-++⁺ʳ rem (∈-++⁺ˡ yInΔ₁)

    subDFromRight : ∀ {y : PFormula}
      → y ∈ (rem ++ Δ₂')
      → y ∈ rhsTarget
    subDFromRight {y} yInR with ∈-++⁻ rem {ys = Δ₂'} yInR
    ... | inl yInRem = ∈-++⁺ˡ yInRem
    ... | inr yInΔ₂ = ∈-++⁺ʳ rem (∈-++⁺ʳ Δ₁' yInΔ₂)

    subD : ((rem ++ Δ₁') ++ (rem ++ Δ₂')) ⊆ rhsTarget
    subD {y} yIn with ∈-++⁻ (rem ++ Δ₁') {ys = rem ++ Δ₂'} yIn
    ... | inl yInL = subDFromLeft yInL
    ... | inr yInR = subDFromRight yInR

    Πmid : lhsExpanded ⊢ rhsTarget
    Πmid = structural subL subD Πcut₀

    dΠmid≤n : δ Πmid ≤ n
    dΠmid≤n =
      snd (structural-δ subL subD Πcut₀ dΠcut₀≤n)

    lhsEq : lhsExpanded ≡ (Γ ++ ((Γ₁' ++ Γ₂') -pf (A ^ α)))
    lhsEq = cong (Γ ++_) (sym (pf-++ (A ^ α) Γ₁' Γ₂'))

    Πres : (Γ ++ ((Γ₁' ++ Γ₂') -pf (A ^ α)))
       ⊢ ((Δ -pf (A ^ α)) ++ (Δ₁' ++ Δ₂'))
    Πres = subst (λ xs → xs ⊢ rhsTarget) lhsEq Πmid

    dΠres≤n : δ Πres ≤ n
    dΠres≤n =
      snd (subst-δ-Γ lhsEq Πmid dΠmid≤n)

mix-lift-right-BoxL :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → Neg ((□ B ^ β) ≡ (A ^ α))
  → modalConstraint M β γ (Γ ++ (Γ' -pf (A ^ α))) ((Δ -pf (A ^ α)) ++ Δ')
  → (n : ℕ)
  → Σ ((Γ ++ ((Γ' ++ [ (B ^ γ) ]) -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ ((Γ' ++ [ (□ B ^ β) ]) -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
mix-lift-right-BoxL
  {Γ} {Δ} {Γ'} {Δ'} {A} {B} {α} {β} {γ}
  box≢a mc' n (Π₀ , dΠ₀≤n) =
  bCase ((B ^ γ) ≟pf (A ^ α))
  where
    rem : Ctx
    rem = Γ' -pf (A ^ α)

    rhs : Ctx
    rhs = (Δ -pf (A ^ α)) ++ Δ'

    eqBoxSingle : ([ (□ B ^ β) ] -pf (A ^ α)) ≡ [ (□ B ^ β) ]
    eqBoxSingle = pf-singleton-neq (λ q → box≢a (sym q))

    eqBoxRem : ((Γ' ++ [ (□ B ^ β) ]) -pf (A ^ α))
            ≡ (rem ++ [ (□ B ^ β) ])
    eqBoxRem =
      pf-++ (A ^ α) Γ' [ (□ B ^ β) ]
      ∙ cong (rem ++_) eqBoxSingle

    eqBoxCtx : (Γ ++ ((Γ' ++ [ (□ B ^ β) ]) -pf (A ^ α)))
            ≡ (Γ ++ (rem ++ [ (□ B ^ β) ]))
    eqBoxCtx = cong (Γ ++_) eqBoxRem

    bCase : Dec ((B ^ γ) ≡ (A ^ α))
      → Σ ((Γ ++ ((Γ' ++ [ (□ B ^ β) ]) -pf (A ^ α)))
          ⊢ rhs)
          (λ Π₀ → δ Π₀ ≤ n)

    bCase (yes eqBA) =
      Πres , dΠres≤n
      where
        eqSingle : ([ (B ^ γ) ] -pf (A ^ α)) ≡ []
        eqSingle =
          pf-cons-eq
            {φ = (A ^ α)} {ψ = (B ^ γ)} {Γ = []}
            eqBA

        eqBRem : ((Γ' ++ [ (B ^ γ) ]) -pf (A ^ α))
              ≡ (rem ++ [])
        eqBRem =
          pf-++ (A ^ α) Γ' [ (B ^ γ) ]
          ∙ cong (rem ++_) eqSingle

        eqBCtx : (Γ ++ ((Γ' ++ [ (B ^ γ) ]) -pf (A ^ α)))
              ≡ (Γ ++ (rem ++ []))
        eqBCtx = cong (Γ ++_) eqBRem

        Πmid₀ : (Γ ++ (rem ++ [])) ⊢ rhs
        Πmid₀ = subst (λ xs → xs ⊢ rhs) eqBCtx Π₀

        dΠmid₀≤n : δ Πmid₀ ≤ n
        dΠmid₀≤n = snd (subst-δ-Γ eqBCtx Π₀ dΠ₀≤n)

        subL₀ : (Γ ++ (rem ++ [])) ⊆ (Γ ++ rem)
        subL₀ = solveCtx⊆!

        Πbase : (Γ ++ rem) ⊢ rhs
        Πbase = structural subL₀ subset-refl Πmid₀

        dΠbase≤n : δ Πbase ≤ n
        dΠbase≤n =
          snd (structural-δ subL₀ subset-refl Πmid₀ dΠmid₀≤n)

        subL₁ : (Γ ++ rem) ⊆ ((Γ ++ rem) ++ [ (B ^ γ) ])
        subL₁ = solveCtx⊆!

        Πprem : ((Γ ++ rem) ++ [ (B ^ γ) ]) ⊢ rhs
        Πprem = structural subL₁ subset-refl Πbase

        dΠprem≤n : δ Πprem ≤ n
        dΠprem≤n =
          snd (structural-δ subL₁ subset-refl Πbase dΠbase≤n)

        Πbox : ((Γ ++ rem) ++ [ (□ B ^ β) ]) ⊢ rhs
        Πbox = BoxL mc' Πprem

        subL₂ : ((Γ ++ rem) ++ [ (□ B ^ β) ]) ⊆ (Γ ++ (rem ++ [ (□ B ^ β) ]))
        subL₂ = solveCtx⊆!

        Πmid : (Γ ++ (rem ++ [ (□ B ^ β) ])) ⊢ rhs
        Πmid = structural subL₂ subset-refl Πbox

        dΠmid≤n : δ Πmid ≤ n
        dΠmid≤n = snd (structural-δ subL₂ subset-refl Πbox dΠprem≤n)

        Πres : (Γ ++ ((Γ' ++ [ (□ B ^ β) ]) -pf (A ^ α))) ⊢ rhs
        Πres = subst (λ xs → xs ⊢ rhs) (sym eqBoxCtx) Πmid

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Γ (sym eqBoxCtx) Πmid dΠmid≤n)

    bCase (no b≢a) =
      Πres , dΠres≤n
      where
        eqSingle : ([ (B ^ γ) ] -pf (A ^ α)) ≡ [ (B ^ γ) ]
        eqSingle = pf-singleton-neq (λ q → b≢a (sym q))

        eqBRem : ((Γ' ++ [ (B ^ γ) ]) -pf (A ^ α))
              ≡ (rem ++ [ (B ^ γ) ])
        eqBRem =
          pf-++ (A ^ α) Γ' [ (B ^ γ) ]
          ∙ cong (rem ++_) eqSingle

        eqBCtx : (Γ ++ ((Γ' ++ [ (B ^ γ) ]) -pf (A ^ α)))
              ≡ (Γ ++ (rem ++ [ (B ^ γ) ]))
        eqBCtx = cong (Γ ++_) eqBRem

        Πmid₀ : (Γ ++ (rem ++ [ (B ^ γ) ])) ⊢ rhs
        Πmid₀ = subst (λ xs → xs ⊢ rhs) eqBCtx Π₀

        dΠmid₀≤n : δ Πmid₀ ≤ n
        dΠmid₀≤n = snd (subst-δ-Γ eqBCtx Π₀ dΠ₀≤n)

        subL₁ : (Γ ++ (rem ++ [ (B ^ γ) ])) ⊆ ((Γ ++ rem) ++ [ (B ^ γ) ])
        subL₁ = solveCtx⊆!

        Πprem : ((Γ ++ rem) ++ [ (B ^ γ) ]) ⊢ rhs
        Πprem = structural subL₁ subset-refl Πmid₀

        dΠprem≤n : δ Πprem ≤ n
        dΠprem≤n =
          snd (structural-δ subL₁ subset-refl Πmid₀ dΠmid₀≤n)

        Πbox : ((Γ ++ rem) ++ [ (□ B ^ β) ]) ⊢ rhs
        Πbox = BoxL mc' Πprem

        subL₂ : ((Γ ++ rem) ++ [ (□ B ^ β) ]) ⊆ (Γ ++ (rem ++ [ (□ B ^ β) ]))
        subL₂ = solveCtx⊆!

        Πmid : (Γ ++ (rem ++ [ (□ B ^ β) ])) ⊢ rhs
        Πmid = structural subL₂ subset-refl Πbox

        dΠmid≤n : δ Πmid ≤ n
        dΠmid≤n = snd (structural-δ subL₂ subset-refl Πbox dΠprem≤n)

        Πres : (Γ ++ ((Γ' ++ [ (□ B ^ β) ]) -pf (A ^ α))) ⊢ rhs
        Πres = subst (λ xs → xs ⊢ rhs) (sym eqBoxCtx) Πmid

        dΠres≤n : δ Πres ≤ n
        dΠres≤n =
          snd (subst-δ-Γ (sym eqBoxCtx) Πmid dΠmid≤n)

mix-lift-right-DiaR :
  ∀ {Γ Δ Γ' Δ'} {A B : Formula} {α β γ : Position}
  → Neg ((♢ B ^ β) ≡ (A ^ α))
  → modalConstraint M β γ (Γ ++ (Γ' -pf (A ^ α))) ((Δ -pf (A ^ α)) ++ Δ')
  → (n : ℕ)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ [ (B ^ γ) ] ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
  → Σ ((Γ ++ (Γ' -pf (A ^ α)))
      ⊢ ((Δ -pf (A ^ α)) ++ [ (♢ B ^ β) ] ++ Δ'))
      (λ Π₀ → δ Π₀ ≤ n)
mix-lift-right-DiaR
  {Γ} {Δ} {Γ'} {Δ'} {A} {B} {α} {β} {γ}
  dia≢a mc' n (Π₀ , dΠ₀≤n) =
  Πres , dΠres≤n
  where
    lhs : Ctx
    lhs = Γ ++ (Γ' -pf (A ^ α))

    subD₁ : ((Δ -pf (A ^ α)) ++ [ (B ^ γ) ] ++ Δ')
        ⊆ ((B ^ γ) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    subD₁ = subset-append-mid-cons (Δ -pf (A ^ α)) Δ' (B ^ γ)

    Πprem : lhs ⊢ ((B ^ γ) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    Πprem = structural subset-refl subD₁ Π₀

    dΠprem≤n : δ Πprem ≤ n
    dΠprem≤n =
      snd (structural-δ subset-refl subD₁ Π₀ dΠ₀≤n)

    Πdia : lhs ⊢ ((♢ B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
    Πdia = DiaR mc' Πprem

    subD₂ : ((♢ B ^ β) ∷ ((Δ -pf (A ^ α)) ++ Δ'))
        ⊆ ((Δ -pf (A ^ α)) ++ [ (♢ B ^ β) ] ++ Δ')
    subD₂ = subset-cons-append-mid (Δ -pf (A ^ α)) Δ' (♢ B ^ β)

    Πres : lhs ⊢ ((Δ -pf (A ^ α)) ++ [ (♢ B ^ β) ] ++ Δ')
    Πres = structural subset-refl subD₂ Πdia

    dΠres≤n : δ Πres ≤ n
    dΠres≤n =
      snd (structural-δ subset-refl subD₂ Πdia dΠprem≤n)

-- TODO: full serial/non-serial recursive Mix proof (`mix : MixAPI`).

{-# TERMINATING #-}
mixWorkerRaw : ∀ {Γ Δ Γ' Δ'} {A : Formula} {α : Position}
  → (n : ℕ) → degree A ≡ n
  → (Π : Γ ⊢ Δ) → (Π' : Γ' ⊢ Δ')
  → cutConstraint M A α Γ Γ' Δ Δ'
  → Acc _<Lex_ (n , mixHeight Π Π')
  → MixResult (max (δ Π) (δ Π')) {Γ} {Δ} {Γ'} {Δ'} {A} {α}
mixWorkerRaw {Γ} {Δ} {Γ'} {Δ'} {A} {α} n degEq Π Π' c wf =
  mixGo {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ'} {Δ₀' = Δ'} Π Π' c wf
  where
    mutual
      mixGo : ∀ {Γ₀ Δ₀ Γ₀' Δ₀'}
        → (Π₀ : Γ₀ ⊢ Δ₀) → (Π₀' : Γ₀' ⊢ Δ₀')
        → cutConstraint M A α Γ₀ Γ₀' Δ₀ Δ₀'
        → Acc _<Lex_ (n , mixHeight Π₀ Π₀')
        → MixResult (max (δ Π₀) (δ Π₀')) {Γ₀} {Δ₀} {Γ₀'} {Δ₀'} {A} {α}
      -- Base: Ax on left
      mixGo (Ax {A = B} {α = β}) Π₀' c _ =
        mix-left-Ax {A = A} {B = B} {α = α} {β = β}
          (max 0 (δ Π₀')) Π₀' (right-≤-max {n = δ Π₀'} {m = 0})
      -- Base: Ax on right (left is not Ax, caught above)
      mixGo Π₀ (Ax {A = B} {α = β}) c _ =
        mix-right-Ax {A = A} {B = B} {α = α} {β = β}
          (max (δ Π₀) 0) Π₀ (left-≤-max {m = δ Π₀} {n = 0})
      -- Structural left
      mixGo {Γ₀ = (C ^ γ) ∷ Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
        (WeakenL {A = C} {α = γ} Πsub) Π₀' c (acc rec)
        with cutConstraint-down-left-WeakenL
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
          {A = A} {C = C} {α = α} {γ = γ} c
      ... | just c↓ =
        mix-lift-left-WeakenL
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
          {A = A} {C = C} {α = α} {γ = γ}
          (max (δ Πsub) (δ Π₀'))
          (mixGo {Γ₀ = Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'} Πsub Π₀' c↓
            (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
      ... | nothing = mixGoR (WeakenL {A = C} {α = γ} Πsub) Π₀' c (acc rec)
      mixGo {Γ₀ = Γ₁} {Δ₀ = (C ^ γ) ∷ Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
        (WeakenR {A = C} {α = γ} Πsub) Π₀' c (acc rec)
        with cutConstraint-down-left-WeakenR
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
          {A = A} {C = C} {α = α} {γ = γ} c
      ... | just c↓ =
        mix-lift-left-WeakenR
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
          {A = A} {C = C} {α = α} {γ = γ}
          (max (δ Πsub) (δ Π₀'))
          (mixGo {Γ₀ = Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'} Πsub Π₀' c↓
            (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
      ... | nothing = mixGoR (WeakenR {A = C} {α = γ} Πsub) Π₀' c (acc rec)
      mixGo {Γ₀ = (C ^ γ) ∷ Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
        (ContractL {A = C} {α = γ} Πsub) Π₀' c (acc rec) =
        mix-lift-left-ContractL
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
          {A = A} {C = C} {α = α} {γ = γ}
          (max (δ Πsub) (δ Π₀'))
          (mixGo
            {Γ₀ = (C ^ γ) ∷ (C ^ γ) ∷ Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
            Πsub Π₀'
            (cutConstraint-up-left-ContractL
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
              {A = A} {C = C} {α = α} {γ = γ} c)
            (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
      mixGo {Γ₀ = Γ₁} {Δ₀ = (C ^ γ) ∷ Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
        (ContractR {A = C} {α = γ} Πsub) Π₀' c (acc rec) =
        mix-lift-left-ContractR
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
          {A = A} {C = C} {α = α} {γ = γ}
          (max (δ Πsub) (δ Π₀'))
          (mixGo
            {Γ₀ = Γ₁} {Δ₀ = (C ^ γ) ∷ (C ^ γ) ∷ Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
            Πsub Π₀'
            (cutConstraint-up-left-ContractR
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
              {A = A} {C = C} {α = α} {γ = γ} c)
            (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
      mixGo {Δ₀ = Δ₀} {Γ₀' = Γ₀'} {Δ₀' = Δ₀'}
        (ExchangeL {Γ₁ = Γ₁} {Γ₂ = Γ₂} {C = c₁} {D = d₁} Πsub)
        Π₀' c (acc rec) =
        mix-lift-left-ExchangeL
          {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ = Δ₀} {Γ' = Γ₀'} {Δ' = Δ₀'}
          {A = A} {α = α} {c = c₁} {d = d₁}
          (max (δ Πsub) (δ Π₀'))
          (mixGo Πsub Π₀'
            (cutConstraint-down-left-ExchangeL
              {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ' = Γ₀'} {Δ = Δ₀} {Δ' = Δ₀'}
              {A = A} {α = α} {c = c₁} {d = d₁} c)
            (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
      mixGo {Γ₀ = Γ₀} {Γ₀' = Γ₀'} {Δ₀' = Δ₀'}
        (ExchangeR {Δ₁ = Δ₁} {Δ₂ = Δ₂} {C = c₁} {D = d₁} Πsub)
        Π₀' c (acc rec) =
        mix-lift-left-ExchangeR
          {Γ = Γ₀} {Δ₁ = Δ₁} {Δ₂ = Δ₂} {Γ' = Γ₀'} {Δ' = Δ₀'}
          {A = A} {α = α} {c = c₁} {d = d₁}
          (max (δ Πsub) (δ Π₀'))
          (mixGo Πsub Π₀'
            (cutConstraint-down-left-ExchangeR
              {Γ = Γ₀} {Γ' = Γ₀'} {Δ' = Δ₀'} {Δ₁ = Δ₁} {Δ₂ = Δ₂}
              {A = A} {α = α} {c = c₁} {d = d₁} c)
            (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
      -- Logical unary left
      mixGo {Γ₀ = (Not B ^ β) ∷ Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
        (NotL {A = B} {α = β} Πsub) Π₀' c (acc rec)
        with cutConstraint-down-left-NotL
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
          {A = A} {B = B} {α = α} {β = β} c
      ... | just c↓ =
        mix-lift-left-NotL
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
          {A = A} {B = B} {α = α} {β = β}
          (max (δ Πsub) (δ Π₀'))
          (mixGo {Γ₀ = Γ₁} {Δ₀ = (B ^ β) ∷ Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
            Πsub Π₀' c↓
            (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
      ... | nothing = mixGoR (NotL {A = B} {α = β} Πsub) Π₀' c (acc rec)
      mixGo {Γ₀ = Γ₁} {Δ₀ = (Not B ^ β) ∷ Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
        (NotR {A = B} {α = β} Πsub) Π₀' c (acc rec) =
        notRCase ((Not B ^ β) ≟pf (A ^ α))
        where
          notRCase : Dec ((Not B ^ β) ≡ (A ^ α))
            → MixResult (max (δ Πsub) (δ Π₀'))
                {Γ = Γ₁} {Δ = (Not B ^ β) ∷ Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'} {A = A} {α = α}
          notRCase (yes _) = mixGoR (NotR {A = B} {α = β} Πsub) Π₀' c (acc rec)
          notRCase (no notB≢A) =
            mix-lift-left-NotR
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
              {A = A} {B = B} {α = α} {β = β}
              notB≢A (max (δ Πsub) (δ Π₀'))
              (mixGo {Γ₀ = (B ^ β) ∷ Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
                Πsub Π₀'
                (cutConstraint-down-left-NotR
                  {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
                  {A = A} {B = B} {α = α} {β = β} c)
                (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
      mixGo {Γ₀ = (And B C ^ β) ∷ Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
        (AndL1 {B = C} Πsub) Π₀' c (acc rec) =
        mix-lift-left-AndL1
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
          {A = A} {B = B} {C = C} {α = α} {β = β}
          (max (δ Πsub) (δ Π₀'))
          (mixGo {Γ₀ = (B ^ β) ∷ Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
            Πsub Π₀'
            (cutConstraint-down-left-AndL1
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c)
            (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
      mixGo {Γ₀ = (And B C ^ β) ∷ Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
        (AndL2 {A = B} Πsub) Π₀' c (acc rec) =
        mix-lift-left-AndL2
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
          {A = A} {B = B} {C = C} {α = α} {β = β}
          (max (δ Πsub) (δ Π₀'))
          (mixGo {Γ₀ = (C ^ β) ∷ Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
            Πsub Π₀'
            (cutConstraint-down-left-AndL2
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c)
            (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
      mixGo {Γ₀ = Γ₁} {Δ₀ = (Or B C ^ β) ∷ Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
        (OrR1 {B = C} Πsub) Π₀' c (acc rec) =
        orR1Case ((Or B C ^ β) ≟pf (A ^ α))
        where
          orR1Case : Dec ((Or B C ^ β) ≡ (A ^ α))
            → MixResult (max (δ Πsub) (δ Π₀'))
                {Γ = Γ₁} {Δ = (Or B C ^ β) ∷ Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'} {A = A} {α = α}
          orR1Case (yes _) = mixGoR (OrR1 {B = C} Πsub) Π₀' c (acc rec)
          orR1Case (no or≢a)
            with cutConstraint-down-left-OrR1
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c↓ =
            mix-lift-left-OrR1
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
              {A = A} {B = B} {C = C} {α = α} {β = β}
              or≢a (max (δ Πsub) (δ Π₀'))
              (mixGo {Γ₀ = Γ₁} {Δ₀ = (B ^ β) ∷ Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
                Πsub Π₀' c↓
                (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
          ... | nothing = mixGoR (OrR1 {B = C} Πsub) Π₀' c (acc rec)
      mixGo {Γ₀ = Γ₁} {Δ₀ = (Or B C ^ β) ∷ Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
        (OrR2 {A = B} Πsub) Π₀' c (acc rec) =
        orR2Case ((Or B C ^ β) ≟pf (A ^ α))
        where
          orR2Case : Dec ((Or B C ^ β) ≡ (A ^ α))
            → MixResult (max (δ Πsub) (δ Π₀'))
                {Γ = Γ₁} {Δ = (Or B C ^ β) ∷ Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'} {A = A} {α = α}
          orR2Case (yes _) = mixGoR (OrR2 {A = B} Πsub) Π₀' c (acc rec)
          orR2Case (no or≢a)
            with cutConstraint-down-left-OrR2
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c↓ =
            mix-lift-left-OrR2
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
              {A = A} {B = B} {C = C} {α = α} {β = β}
              or≢a (max (δ Πsub) (δ Π₀'))
              (mixGo {Γ₀ = Γ₁} {Δ₀ = (C ^ β) ∷ Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
                Πsub Π₀' c↓
                (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
          ... | nothing = mixGoR (OrR2 {A = B} Πsub) Π₀' c (acc rec)
      mixGo {Γ₀ = Γ₁} {Δ₀ = ((B ⇒ C) ^ β) ∷ Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
        (ImpR {A = B} {α = β} {B = C} Πsub) Π₀' c (acc rec) =
        impCase (((B ⇒ C) ^ β) ≟pf (A ^ α))
        where
          impCase : Dec (((B ⇒ C) ^ β) ≡ (A ^ α))
            → MixResult (max (δ Πsub) (δ Π₀'))
                {Γ = Γ₁} {Δ = ((B ⇒ C) ^ β) ∷ Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'} {A = A} {α = α}
          impCase (yes _) = mixGoR (ImpR {A = B} {α = β} {B = C} Πsub) Π₀' c (acc rec)
          impCase (no imp≢a)
            with cutConstraint-down-left-ImpR
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c↓ =
            mix-lift-left-ImpR
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₁'} {Δ' = Δ₁'}
              {A = A} {B = B} {C = C} {α = α} {β = β}
              imp≢a (max (δ Πsub) (δ Π₀'))
              (mixGo {Γ₀ = (B ^ β) ∷ Γ₁} {Δ₀ = (C ^ β) ∷ Δ₁} {Γ₀' = Γ₁'} {Δ₀' = Δ₁'}
                Πsub Π₀' c↓
                (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
          ... | nothing = mixGoR (ImpR {A = B} {α = β} {B = C} Πsub) Π₀' c (acc rec)
      -- Binary left
      mixGo
        {Γ₀' = Γr} {Δ₀' = Δr}
        (AndR {Γ₁ = Γ₁} {A = B} {α = β} {Δ₁ = Δ₁}
              {Γ₂ = Γ₂} {B = C} {Δ₂ = Δ₂} Π₁ Π₂)
        Π₀' c (acc rec) =
        andRCase ((And B C ^ β) ≟pf (A ^ α))
        where
          andRCase : Dec ((And B C ^ β) ≡ (A ^ α))
            → MixResult (max (max (δ Π₁) (δ Π₂)) (δ Π₀'))
                {Γ = Γ₁ ++ Γ₂} {Δ = (And B C ^ β) ∷ (Δ₁ ++ Δ₂)}
                {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
          andRCase (yes _) = mixGoR (AndR Π₁ Π₂) Π₀' c (acc rec)
          andRCase (no and≢a)
            with cutConstraint-down-left-AndR₁
              {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Γ₂ = Γ₂} {Δ₂ = Δ₂} {Γ' = Γr} {Δ' = Δr}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
               | cutConstraint-down-left-AndR₂
              {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Γ₂ = Γ₂} {Δ₂ = Δ₂} {Γ' = Γr} {Δ' = Δr}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c₁ | just c₂ =
            mix-lift-left-AndR
              {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ₁ = Δ₁} {Δ₂ = Δ₂}
              {Γ' = Γr} {Δ' = Δr} {A = A} {B = B} {C = C} {α = α} {β = β}
              and≢a (max (max (δ Π₁) (δ Π₂)) (δ Π₀'))
              (liftMixResult
                {m = max (δ Π₁) (δ Π₀')}
                {n = max (max (δ Π₁) (δ Π₂)) (δ Π₀')}
                {Γ = Γ₁} {Δ = (B ^ β) ∷ Δ₁} {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
                (max-least
                  (≤-trans
                    (left-≤-max {m = δ Π₁} {n = δ Π₂})
                    (left-≤-max {m = max (δ Π₁) (δ Π₂)} {n = δ Π₀'}))
                  (right-≤-max {n = δ Π₀'} {m = max (δ Π₁) (δ Π₂)}))
                (mixGo
                  {Γ₀ = Γ₁} {Δ₀ = (B ^ β) ∷ Δ₁} {Γ₀' = Γr} {Δ₀' = Δr}
                  Π₁ Π₀' c₁
                  (rec _ (step-lex-height (step-left-binary₁ (height Π₁) (height Π₂) (height Π₀'))))))
              (liftMixResult
                {m = max (δ Π₂) (δ Π₀')}
                {n = max (max (δ Π₁) (δ Π₂)) (δ Π₀')}
                {Γ = Γ₂} {Δ = (C ^ β) ∷ Δ₂} {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
                (max-least
                  (≤-trans
                    (right-≤-max {n = δ Π₂} {m = δ Π₁})
                    (left-≤-max {m = max (δ Π₁) (δ Π₂)} {n = δ Π₀'}))
                  (right-≤-max {n = δ Π₀'} {m = max (δ Π₁) (δ Π₂)}))
                (mixGo
                  {Γ₀ = Γ₂} {Δ₀ = (C ^ β) ∷ Δ₂} {Γ₀' = Γr} {Δ₀' = Δr}
                  Π₂ Π₀' c₂
                  (rec _ (step-lex-height (step-left-binary₂ (height Π₁) (height Π₂) (height Π₀'))))))
          ... | _ | _ = mixGoR (AndR Π₁ Π₂) Π₀' c (acc rec)
      mixGo
        {Γ₀' = Γr} {Δ₀' = Δr}
        (OrL {A = B} {α = β} {Γ₁ = Γ₁} {Δ₁ = Δ₁}
             {B = C} {Γ₂ = Γ₂} {Δ₂ = Δ₂} Π₁ Π₂)
        Π₀' c (acc rec) =
        orLCase ((Or B C ^ β) ≟pf (A ^ α))
        where
          orLCase : Dec ((Or B C ^ β) ≡ (A ^ α))
            → MixResult (max (max (δ Π₁) (δ Π₂)) (δ Π₀'))
                {Γ = (Or B C ^ β) ∷ (Γ₁ ++ Γ₂)} {Δ = Δ₁ ++ Δ₂}
                {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
          orLCase (yes _) = mixGoR (OrL Π₁ Π₂) Π₀' c (acc rec)
          orLCase (no or≢a)
            with cutConstraint-down-left-OrL₁
              {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Γ₂ = Γ₂} {Δ₂ = Δ₂} {Γ' = Γr} {Δ' = Δr}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
               | cutConstraint-down-left-OrL₂
              {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Γ₂ = Γ₂} {Δ₂ = Δ₂} {Γ' = Γr} {Δ' = Δr}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c₁ | just c₂ =
            mix-lift-left-OrL
              {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ₁ = Δ₁} {Δ₂ = Δ₂}
              {Γ' = Γr} {Δ' = Δr} {A = A} {B = B} {C = C} {α = α} {β = β}
              or≢a (max (max (δ Π₁) (δ Π₂)) (δ Π₀'))
              (liftMixResult
                {m = max (δ Π₁) (δ Π₀')}
                {n = max (max (δ Π₁) (δ Π₂)) (δ Π₀')}
                {Γ = (B ^ β) ∷ Γ₁} {Δ = Δ₁} {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
                (max-least
                  (≤-trans
                    (left-≤-max {m = δ Π₁} {n = δ Π₂})
                    (left-≤-max {m = max (δ Π₁) (δ Π₂)} {n = δ Π₀'}))
                  (right-≤-max {n = δ Π₀'} {m = max (δ Π₁) (δ Π₂)}))
                (mixGo
                  {Γ₀ = (B ^ β) ∷ Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γr} {Δ₀' = Δr}
                  Π₁ Π₀' c₁
                  (rec _ (step-lex-height (step-left-binary₁ (height Π₁) (height Π₂) (height Π₀'))))))
              (liftMixResult
                {m = max (δ Π₂) (δ Π₀')}
                {n = max (max (δ Π₁) (δ Π₂)) (δ Π₀')}
                {Γ = (C ^ β) ∷ Γ₂} {Δ = Δ₂} {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
                (max-least
                  (≤-trans
                    (right-≤-max {n = δ Π₂} {m = δ Π₁})
                    (left-≤-max {m = max (δ Π₁) (δ Π₂)} {n = δ Π₀'}))
                  (right-≤-max {n = δ Π₀'} {m = max (δ Π₁) (δ Π₂)}))
                (mixGo
                  {Γ₀ = (C ^ β) ∷ Γ₂} {Δ₀ = Δ₂} {Γ₀' = Γr} {Δ₀' = Δr}
                  Π₂ Π₀' c₂
                  (rec _ (step-lex-height (step-left-binary₂ (height Π₁) (height Π₂) (height Π₀'))))))
          ... | _ | _ = mixGoR (OrL Π₁ Π₂) Π₀' c (acc rec)
      mixGo
        {Γ₀' = Γr} {Δ₀' = Δr}
        (ImpL {Γ₁ = Γ₁} {A = B} {α = β} {Δ₁ = Δ₁}
              {B = C} {Γ₂ = Γ₂} {Δ₂ = Δ₂} Π₁ Π₂)
        Π₀' c (acc rec) =
        impLCase (((B ⇒ C) ^ β) ≟pf (A ^ α))
        where
          impLCase : Dec (((B ⇒ C) ^ β) ≡ (A ^ α))
            → MixResult (max (max (δ Π₁) (δ Π₂)) (δ Π₀'))
                {Γ = ((B ⇒ C) ^ β) ∷ (Γ₁ ++ Γ₂)} {Δ = Δ₁ ++ Δ₂}
                {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
          impLCase (yes _) = mixGoR (ImpL Π₁ Π₂) Π₀' c (acc rec)
          impLCase (no imp≢a)
            with cutConstraint-down-left-ImpL₁
              {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Γ₂ = Γ₂} {Δ₂ = Δ₂} {Γ' = Γr} {Δ' = Δr}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
               | cutConstraint-down-left-ImpL₂
              {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Γ₂ = Γ₂} {Δ₂ = Δ₂} {Γ' = Γr} {Δ' = Δr}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c₁ | just c₂ =
            mix-lift-left-ImpL
              {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ₁ = Δ₁} {Δ₂ = Δ₂}
              {Γ' = Γr} {Δ' = Δr} {A = A} {B = B} {C = C} {α = α} {β = β}
              imp≢a (max (max (δ Π₁) (δ Π₂)) (δ Π₀'))
              (liftMixResult
                {m = max (δ Π₁) (δ Π₀')}
                {n = max (max (δ Π₁) (δ Π₂)) (δ Π₀')}
                {Γ = Γ₁} {Δ = (B ^ β) ∷ Δ₁} {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
                (max-least
                  (≤-trans
                    (left-≤-max {m = δ Π₁} {n = δ Π₂})
                    (left-≤-max {m = max (δ Π₁) (δ Π₂)} {n = δ Π₀'}))
                  (right-≤-max {n = δ Π₀'} {m = max (δ Π₁) (δ Π₂)}))
                (mixGo
                  {Γ₀ = Γ₁} {Δ₀ = (B ^ β) ∷ Δ₁} {Γ₀' = Γr} {Δ₀' = Δr}
                  Π₁ Π₀' c₁
                  (rec _ (step-lex-height (step-left-binary₁ (height Π₁) (height Π₂) (height Π₀'))))))
              (liftMixResult
                {m = max (δ Π₂) (δ Π₀')}
                {n = max (max (δ Π₁) (δ Π₂)) (δ Π₀')}
                {Γ = (C ^ β) ∷ Γ₂} {Δ = Δ₂} {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
                (max-least
                  (≤-trans
                    (right-≤-max {n = δ Π₂} {m = δ Π₁})
                    (left-≤-max {m = max (δ Π₁) (δ Π₂)} {n = δ Π₀'}))
                  (right-≤-max {n = δ Π₀'} {m = max (δ Π₁) (δ Π₂)}))
                (mixGo
                  {Γ₀ = (C ^ β) ∷ Γ₂} {Δ₀ = Δ₂} {Γ₀' = Γr} {Δ₀' = Δr}
                  Π₂ Π₀' c₂
                  (rec _ (step-lex-height (step-left-binary₂ (height Π₁) (height Π₂) (height Π₀'))))))
          ... | _ | _ = mixGoR (ImpL Π₁ Π₂) Π₀' c (acc rec)
      -- Cut on left
      mixGo {Γ₀' = Γr} {Δ₀' = Δr}
        (Cut {A = A'} {α = α'} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ₁ = Δ₁} {Δ₂ = Δ₂} cCut Π₁ Π₂)
        Π₀' c (acc rec)
        with cutConstraint-down-left-Cut₁
          {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Γ₂ = Γ₂} {Δ₂ = Δ₂} {Γ' = Γr} {Δ' = Δr}
          {A = A} {A' = A'} {α = α} {α' = α'} c
           | cutConstraint-down-left-Cut₂
          {Γ₁ = Γ₁} {Δ₁ = Δ₁} {Γ₂ = Γ₂} {Δ₂ = Δ₂} {Γ' = Γr} {Δ' = Δr}
          {A = A} {A' = A'} {α = α} {α' = α'} c
           | cutConstraint-rebuild
          {A = A'} {α = α'}
          {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ₁ = Δ₁} {Δ₂ = Δ₂}
          {Γ₁' = Γ₁ ++ (Γr -pf (A ^ α))}
          {Γ₂' = Γ₂ ++ (Γr -pf (A ^ α))}
          {Δ₁' = (Δ₁ -pf (A ^ α)) ++ Δr}
          {Δ₂' = (Δ₂ -pf (A ^ α)) ++ Δr}
          cCut
      ... | just c₁ | just c₂ | just cCut' =
        mix-lift-left-Cut
          {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ₁ = Δ₁} {Δ₂ = Δ₂}
          {Γ' = Γr} {Δ' = Δr}
          {A = A} {A' = A'} {α = α} {α' = α'}
          cCut' (max (max (suc (degree A')) (max (δ Π₁) (δ Π₂))) (δ Π₀'))
          (≤-trans
            (left-≤-max {m = suc (degree A')} {n = max (δ Π₁) (δ Π₂)})
            (left-≤-max {m = max (suc (degree A')) (max (δ Π₁) (δ Π₂))} {n = δ Π₀'}))
          (liftMixResult
            {m = max (δ Π₁) (δ Π₀')}
            {n = max (max (suc (degree A')) (max (δ Π₁) (δ Π₂))) (δ Π₀')}
            {Γ = Γ₁} {Δ = [ (A' ^ α') ] ++ Δ₁} {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
            (max-least
              (≤-trans
                (left-≤-max {m = δ Π₁} {n = δ Π₂})
                (≤-trans
                  (right-≤-max {n = max (δ Π₁) (δ Π₂)} {m = suc (degree A')})
                  (left-≤-max {m = max (suc (degree A')) (max (δ Π₁) (δ Π₂))} {n = δ Π₀'})))
              (right-≤-max {n = δ Π₀'} {m = max (suc (degree A')) (max (δ Π₁) (δ Π₂))}))
            (mixGo
              {Γ₀ = Γ₁} {Δ₀ = [ (A' ^ α') ] ++ Δ₁} {Γ₀' = Γr} {Δ₀' = Δr}
              Π₁ Π₀' c₁
              (rec _ (step-lex-height (step-left-binary₁ (height Π₁) (height Π₂) (height Π₀'))))))
          (liftMixResult
            {m = max (δ Π₂) (δ Π₀')}
            {n = max (max (suc (degree A')) (max (δ Π₁) (δ Π₂))) (δ Π₀')}
            {Γ = Γ₂ ++ [ (A' ^ α') ]} {Δ = Δ₂} {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
            (max-least
              (≤-trans
                (right-≤-max {n = δ Π₂} {m = δ Π₁})
                (≤-trans
                  (right-≤-max {n = max (δ Π₁) (δ Π₂)} {m = suc (degree A')})
                  (left-≤-max {m = max (suc (degree A')) (max (δ Π₁) (δ Π₂))} {n = δ Π₀'})))
              (right-≤-max {n = δ Π₀'} {m = max (suc (degree A')) (max (δ Π₁) (δ Π₂))}))
            (mixGo
              {Γ₀ = Γ₂ ++ [ (A' ^ α') ]} {Δ₀ = Δ₂} {Γ₀' = Γr} {Δ₀' = Δr}
              Π₂ Π₀' c₂
              (rec _ (step-lex-height (step-left-binary₂ (height Π₁) (height Π₂) (height Π₀'))))))
      ... | _ | _ | _ = mixGoR (Cut cCut Π₁ Π₂) Π₀' c (acc rec)
      -- Modal left
      mixGo {Γ₀' = Γr} {Δ₀' = Δr}
        (BoxL {Γ = Γ₁} {Δ = Δ₁} {A = B} {α = β} {β = γ} mc Πsub)
        Π₀' c (acc rec) =
        boxLCase ((□ B ^ β) ≟pf (A ^ α))
        where
          boxLCase : Dec ((□ B ^ β) ≡ (A ^ α))
            → MixResult (max (δ Πsub) (δ Π₀'))
                {Γ = Γ₁ ++ [ (□ B ^ β) ]} {Δ = Δ₁}
                {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
          boxLCase (yes _) = mixGoR (BoxL mc Πsub) Π₀' c (acc rec)
          boxLCase (no box≢a)
            with modalConstraint-rebuild
              {α = β} {β = γ}
              {Γ = Γ₁} {Δ = Δ₁}
              {Γ' = Γ₁ ++ (Γr -pf (A ^ α))}
              {Δ' = (Δ₁ -pf (A ^ α)) ++ Δr}
              mc
          ... | nothing = mixGoR (BoxL mc Πsub) Π₀' c (acc rec)
          ... | just mc' =
            mix-lift-left-BoxL
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γr} {Δ' = Δr}
              {A = A} {B = B} {α = α} {β = β} {γ = γ}
              box≢a mc' (max (δ Πsub) (δ Π₀'))
              (mixGo {Γ₀ = Γ₁ ++ [ (B ^ γ) ]} {Δ₀ = Δ₁} {Γ₀' = Γr} {Δ₀' = Δr}
                Πsub Π₀'
                (cutConstraint-down-left-BoxL
                  {A = A} {B = B} {α = α} {β = β} {γ = γ}
                  mc c)
                (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
      mixGo (BoxR fr Πsub) Π₀' c wf = mixGoR (BoxR fr Πsub) Π₀' c wf
      mixGo (DiaL fr Πsub) Π₀' c wf = mixGoR (DiaL fr Πsub) Π₀' c wf
      mixGo {Γ₀' = Γr} {Δ₀' = Δr}
        (DiaR {Γ = Γ₁} {Δ = Δ₁} {A = B} {α = β} {β = γ} mc Πsub)
        Π₀' c (acc rec) =
        diaRCase ((♢ B ^ β) ≟pf (A ^ α))
        where
          diaRCase : Dec ((♢ B ^ β) ≡ (A ^ α))
            → MixResult (max (δ Πsub) (δ Π₀'))
                {Γ = Γ₁} {Δ = (♢ B ^ β) ∷ Δ₁}
                {Γ' = Γr} {Δ' = Δr} {A = A} {α = α}
          diaRCase (yes _) = mixGoR (DiaR mc Πsub) Π₀' c (acc rec)
          diaRCase (no dia≢a)
            with modalConstraint-rebuild
              {α = β} {β = γ}
              {Γ = Γ₁} {Δ = Δ₁}
              {Γ' = Γ₁ ++ (Γr -pf (A ^ α))}
              {Δ' = (Δ₁ -pf (A ^ α)) ++ Δr}
              mc
          ... | nothing = mixGoR (DiaR mc Πsub) Π₀' c (acc rec)
          ... | just mc'
            with cutConstraint-down-left-DiaR
              {A = A} {B = B} {α = α} {β = β} {γ = γ}
              mc c
          ...   | just c↓ =
            mix-lift-left-DiaR
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γr} {Δ' = Δr}
              {A = A} {B = B} {α = α} {β = β} {γ = γ}
              dia≢a mc' (max (δ Πsub) (δ Π₀'))
              (mixGo {Γ₀ = Γ₁} {Δ₀ = [ (B ^ γ) ] ++ Δ₁} {Γ₀' = Γr} {Δ₀' = Δr}
                Πsub Π₀' c↓
                (rec _ (step-lex-height (step-left-+1 (height Πsub) (height Π₀')))))
          ...   | nothing = mixGoR (DiaR mc Πsub) Π₀' c (acc rec)

      mixGoR : ∀ {Γ₀ Δ₀ Γ₀' Δ₀'}
        → (Π₀ : Γ₀ ⊢ Δ₀) → (Π₀' : Γ₀' ⊢ Δ₀')
        → cutConstraint M A α Γ₀ Γ₀' Δ₀ Δ₀'
        → Acc _<Lex_ (n , mixHeight Π₀ Π₀')
        → MixResult (max (δ Π₀) (δ Π₀')) {Γ₀} {Δ₀} {Γ₀'} {Δ₀'} {A} {α}
      mixGoR Π₀ (Ax {A = B} {α = β}) c wf =
        mix-right-Ax {A = A} {B = B} {α = α} {β = β} (max (δ Π₀) 0) Π₀ left-≤-max
      -- Structural right
      mixGoR {Γ₀ = Γ₁} {Δ₀ = Δ₁} {Γ₀' = (C ^ γ) ∷ Γ₂} {Δ₀' = Δ₂}
        Π₀ (WeakenL {A = C} {α = γ} Πsub) c (acc rec)
        with cutConstraint-down-right-WeakenL
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₂} {Δ' = Δ₂}
          {A = A} {C = C} {α = α} {γ = γ} c
      ... | just c↓ =
        mix-lift-right-WeakenL
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₂} {Δ' = Δ₂}
          {A = A} {C = C} {α = α} {γ = γ}
          (max (δ Π₀) (δ Πsub))
          (mixGo {Γ₀ = Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₂} {Δ₀' = Δ₂}
            Π₀ Πsub c↓
            (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))
      ... | nothing = mixGo Π₀ (WeakenL {A = C} {α = γ} Πsub) c (acc rec)
      mixGoR {Γ₀ = Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₂} {Δ₀' = (C ^ γ) ∷ Δ₂}
        Π₀ (WeakenR {A = C} {α = γ} Πsub) c (acc rec)
        with cutConstraint-down-right-WeakenR
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₂} {Δ' = Δ₂}
          {A = A} {C = C} {α = α} {γ = γ} c
      ... | just c↓ =
        mix-lift-right-WeakenR
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₂} {Δ' = Δ₂}
          {A = A} {C = C} {α = α} {γ = γ}
          (max (δ Π₀) (δ Πsub))
          (mixGo {Γ₀ = Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₂} {Δ₀' = Δ₂}
            Π₀ Πsub c↓
            (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))
      ... | nothing = mixGo Π₀ (WeakenR {A = C} {α = γ} Πsub) c (acc rec)
      mixGoR {Γ₀ = Γ₁} {Δ₀ = Δ₁} {Γ₀' = (C ^ γ) ∷ Γ₂} {Δ₀' = Δ₂}
        Π₀ (ContractL {A = C} {α = γ} Πsub) c (acc rec) =
        mix-lift-right-ContractL
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₂} {Δ' = Δ₂}
          {A = A} {C = C} {α = α} {γ = γ}
          (max (δ Π₀) (δ Πsub))
          (mixGo
            {Γ₀ = Γ₁} {Δ₀ = Δ₁} {Γ₀' = (C ^ γ) ∷ (C ^ γ) ∷ Γ₂} {Δ₀' = Δ₂}
            Π₀ Πsub
            (cutConstraint-up-right-ContractL
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₂} {Δ' = Δ₂}
              {A = A} {C = C} {α = α} {γ = γ} c)
            (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))
      mixGoR {Γ₀ = Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₂} {Δ₀' = (C ^ γ) ∷ Δ₂}
        Π₀ (ContractR {A = C} {α = γ} Πsub) c (acc rec) =
        mix-lift-right-ContractR
          {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₂} {Δ' = Δ₂}
          {A = A} {C = C} {α = α} {γ = γ}
          (max (δ Π₀) (δ Πsub))
          (mixGo
            {Γ₀ = Γ₁} {Δ₀ = Δ₁} {Γ₀' = Γ₂} {Δ₀' = (C ^ γ) ∷ (C ^ γ) ∷ Δ₂}
            Π₀ Πsub
            (cutConstraint-up-right-ContractR
              {Γ = Γ₁} {Δ = Δ₁} {Γ' = Γ₂} {Δ' = Δ₂}
              {A = A} {C = C} {α = α} {γ = γ} c)
            (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))
      mixGoR {Γ₀ = Γ} {Δ₀ = Δ} {Δ₀' = Δ'}
        Π₀ (ExchangeL {Γ₁ = Γ₁} {Γ₂ = Γ₂} {C = c₁} {D = d₁} Πsub)
        c (acc rec) =
        mix-lift-right-ExchangeL
          {Γ = Γ} {Δ = Δ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ' = Δ'}
          {A = A} {α = α} {c = c₁} {d = d₁}
          (max (δ Π₀) (δ Πsub))
          (mixGo
            {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ₁ ++ [ c₁ ] ++ [ d₁ ] ++ Γ₂} {Δ₀' = Δ'}
            Π₀ Πsub
            (cutConstraint-down-right-ExchangeL
              {Γ = Γ} {Δ = Δ} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ' = Δ'}
              {A = A} {α = α} {c = c₁} {d = d₁} c)
            (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))
      mixGoR {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ'} {Δ₀' = Δswap}
        Π₀ (ExchangeR {Δ₁ = Δ₁} {Δ₂ = Δ₂} {C = c₁} {D = d₁} Πsub)
        c (acc rec) =
        mix-lift-right-ExchangeR
          {Γ = Γ} {Δ₁ = Δ₁} {Δ₂ = Δ₂} {Γ' = Γ'} {Δ = Δ}
          {A = A} {α = α} {c = c₁} {d = d₁}
          (max (δ Π₀) (δ Πsub))
          (mixGo
            {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ'} {Δ₀' = Δ₁ ++ [ c₁ ] ++ [ d₁ ] ++ Δ₂}
            Π₀ Πsub
            (cutConstraint-down-right-ExchangeR
              {Γ = Γ} {Γ' = Γ'} {Δ = Δ} {Δ₁ = Δ₁} {Δ₂ = Δ₂}
              {A = A} {α = α} {c = c₁} {d = d₁} c)
            (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))
      -- Logical unary right
      mixGoR {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (Not B ^ β) ∷ Γ'} {Δ₀' = Δ'}
        Π₀ (NotL {A = B} {α = β} Πsub) c (acc rec) =
        notLCase Π₀ rec ((Not B ^ β) ≟pf (A ^ α))
        where
          notLCase : (Π : Γ ⊢ Δ)
            → (∀ m → m <Lex (n , mixHeight Π (NotL Πsub)) → Acc _<Lex_ m)
            → Dec ((Not B ^ β) ≡ (A ^ α))
            → MixResult (max (δ Π) (δ Πsub))
                {Γ = Γ} {Δ = Δ} {Γ' = (Not B ^ β) ∷ Γ'} {Δ' = Δ'} {A = A} {α = α}
          notLCase (NotR {A = B'} {α = β'} {Γ = Γl} {Δ = Δl} Πsub-l) rec' (yes eq)
            with (Not B' ^ β') ≟pf (A ^ α)
          ...   | no notB'≢a =
            subst-δ-Δ (cong (_++ Δ') eqSucc) res d-res
            where
              resPair :
                Σ (Γl ++ (((Not B ^ β) ∷ Γ') -pf (A ^ α))
                  ⊢ ((((Not B' ^ β') ∷ Δl) -pf (A ^ α)) ++ Δ'))
                  (λ Π₁ → δ Π₁ ≤ max (δ Πsub-l) (δ Πsub))
              resPair =
                mix-lift-left-NotR
                  {Γ = Γl} {Δ = Δl} {Γ' = (Not B ^ β) ∷ Γ'} {Δ' = Δ'}
                  {A = A} {B = B'} {α = α} {β = β'}
                  notB'≢a (max (δ Πsub-l) (δ Πsub))
                  (mixGo
                    {Γ₀ = (B' ^ β') ∷ Γl} {Δ₀ = Δl}
                    {Γ₀' = (Not B ^ β) ∷ Γ'} {Δ₀' = Δ'}
                    Πsub-l (NotL {A = B} {α = β} Πsub)
                    (cutConstraint-down-left-NotR
                      {Γ = Γl} {Δ = Δl}
                      {Γ' = (Not B ^ β) ∷ Γ'} {Δ' = Δ'}
                      {A = A} {B = B'} {α = α} {β = β'} c)
                    (rec' _ (step-lex-height
                      (step-left-+1 (height Πsub-l) (height (NotL Πsub))))))

              res = fst resPair
              d-res = snd resPair

              eqSucc :
                (((Not B' ^ β') ∷ Δl) -pf (A ^ α))
                ≡ ((Not B' ^ β') ∷ (Δl -pf (A ^ α)))
              eqSucc with (Not B' ^ β') ≟pf (A ^ α)
              ... | yes p = ⊥.elim (notB'≢a p)
              ... | no _ = refl
          ...   | yes eq_left =
            let
              negB-eq : (Not B' ^ β') ≡ (Not B ^ β)
              negB-eq = eq_left ∙ sym eq

              B-eq : B' ≡ B
              B-eq = Not-inj (pf-form negB-eq)

              β-eq : β' ≡ β
              β-eq = pf-pos negB-eq

              Bt-eq : (B' ^ β') ≡ (B ^ β)
              Bt-eq = cong₂ _^_ B-eq β-eq

              degB<n : degree B < n
              degB<n =
                subst (degree B <_) (cong degree (pf-form eq) ∙ degEq) degree-sub-Not

              eqAntR : ((Not B ^ β) ∷ Γ') -pf (A ^ α) ≡ (Γ' -pf (A ^ α))
              eqAntR =
                pf-cons-eq-raw {φ = (A ^ α)} {ψ = (Not B ^ β)} {Γ = Γ'} (sym eq)

              eqSuccL : ((Not B' ^ β') ∷ Δl) -pf (A ^ α) ≡ (Δl -pf (A ^ α))
              eqSuccL =
                pf-cons-eq {φ = (A ^ α)} {ψ = (Not B' ^ β')} {Γ = Δl} eq_left

              Γ'-rem = Γ' -pf (A ^ α)
              Δl-rem = Δl -pf (A ^ α)

              -- CROSS-CUT 1: left height decrease
              (res1 , d-res1) =
                mixGo Πsub-l (NotL Πsub)
                  (cutConstraint-down-left-NotR
                    {Γ = Γl} {Δ = Δl}
                    {Γ' = (Not B ^ β) ∷ Γ'} {Δ' = Δ'}
                    {A = A} {B = B'} {α = α} {β = β'} c)
                  (rec' _ (step-lex-height
                    (step-left-+1 (height Πsub-l) (height (NotL Πsub)))))

              eqAnt1 : ((B' ^ β') ∷ Γl ++ (((Not B ^ β) ∷ Γ') -pf (A ^ α)))
                     ≡ ((B' ^ β') ∷ Γl ++ Γ'-rem)
              eqAnt1 = cong (((B' ^ β') ∷ Γl) ++_) eqAntR
              (res1a , d-res1a) = subst-δ-Γ eqAnt1 res1 d-res1

              eqAnt1b : ((B' ^ β') ∷ (Γl ++ Γ'-rem))
                      ≡ ((B ^ β) ∷ (Γl ++ Γ'-rem))
              eqAnt1b = cong (_∷ (Γl ++ Γ'-rem)) Bt-eq
              (res1-cast , d-res1-cast) = subst-δ-Γ eqAnt1b res1a d-res1a

              -- CROSS-CUT 2: right height decrease
              (res2 , d-res2) =
                mixGo (NotR Πsub-l) Πsub c-notl
                  (rec' _ (step-lex-height
                    (step-right-+1 (height (NotR Πsub-l)) (height Πsub))))

              eqSucc2 : ((((Not B' ^ β') ∷ Δl) -pf (A ^ α)) ++ ((B ^ β) ∷ Δ'))
                      ≡ (Δl-rem ++ ((B ^ β) ∷ Δ'))
              eqSucc2 = cong (_++ ((B ^ β) ∷ Δ')) eqSuccL
              (res2-cast , d-res2-cast) = subst-δ-Δ eqSucc2 res2 d-res2

              -- FINAL MIX ON B at lower degree
              (mix3 , d-mix3) =
                mixWorkerRaw
                  {Γ = Γl ++ Γ'-rem}
                  {Δ = Δl-rem ++ (B ^ β) ∷ Δ'}
                  {Γ' = (B ^ β) ∷ (Γl ++ Γ'-rem)}
                  {Δ' = Δl-rem ++ Δ'}
                  {A = B} {α = β}
                  (degree B) refl
                  res2-cast res1-cast c-mix-B
                  (rec' _ (step-lex-degree degB<n))

              -- Structural contraction
              goalBound = ≤-trans d-mix3 (max-least d-res2-cast d-res1-cast)
              subAnt0 = subset-absorb-right
                (removeAll-head-subset (Γl ++ Γ'-rem) (B ^ β))
              subSucc0 = subset-absorb-left
                (removeAll-mid-subset Δl-rem Δ' (B ^ β))
              (principalRes , d-principalRes) =
                structural-δ subAnt0 subSucc0 mix3 goalBound
              (res-a , d-res-a) =
                subst-δ-Γ (cong (Γl ++_) (sym eqAntR)) principalRes d-principalRes
            in (res-a , d-res-a)
            where
              c-notl-gen :
                (m : Logic)
                → cutConstraint m A α Γl ((Not B ^ β) ∷ Γ') ((Not B' ^ β') ∷ Δl) Δ'
                → cutConstraint m A α Γl Γ' ((Not B' ^ β') ∷ Δl) ((B ^ β) ∷ Δ')
              c-notl-gen K (inl w) = inl w
              c-notl-gen K (inr w) = branchK (∈Init-++⁻ (((Not B ^ β) ∷ Γ') -pf (A ^ α)) w)
                where
                  branchK :
                    (α ∈Init (((Not B ^ β) ∷ Γ') -pf (A ^ α)))
                    ⊎
                    (α ∈Init Δ')
                    → cutConstraint K A α Γl Γ' ((Not B' ^ β') ∷ Δl) ((B ^ β) ∷ Δ')
                  branchK (inr (pf , mΔ' , p)) =
                    inr
                      (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
                        (pf , there mΔ' , p))

                  branchK (inl (pf , mΓRem , p))
                    with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (Not B ^ β) ∷ Γ'} mΓRem
                  ... | yInOrig , y≠A with yInOrig
                  ...   | here pf≡notB =
                      inr
                        (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
                          ((B ^ β) ,
                            here refl ,
                            subst (λ z → α ⊑ z) (cong PFormula.pos pf≡notB) p))
                  ...   | there yInΓ' =
                      inr
                        (∈Init-++⁺ˡ
                          (pf ,
                            pf-keep
                              {x = (A ^ α)} {y = pf} {Γ = Γ'}
                              yInΓ' (λ q → y≠A (sym q)) ,
                            p))

              c-notl-gen K4 (inl w) = inl w
              c-notl-gen K4 (inr w) = branchK4 (∈Init-++⁻ (((Not B ^ β) ∷ Γ') -pf (A ^ α)) w)
                where
                  branchK4 :
                    (α ∈Init (((Not B ^ β) ∷ Γ') -pf (A ^ α)))
                    ⊎
                    (α ∈Init Δ')
                    → cutConstraint K4 A α Γl Γ' ((Not B' ^ β') ∷ Δl) ((B ^ β) ∷ Δ')
                  branchK4 (inr (pf , mΔ' , p)) =
                    inr
                      (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
                        (pf , there mΔ' , p))

                  branchK4 (inl (pf , mΓRem , p))
                    with pf-remove-mem {x = (A ^ α)} {y = pf} {Γ = (Not B ^ β) ∷ Γ'} mΓRem
                  ... | yInOrig , y≠A with yInOrig
                  ...   | here pf≡notB =
                      inr
                        (∈Init-++⁺ʳ (Γ' -pf (A ^ α))
                          ((B ^ β) ,
                            here refl ,
                            subst (λ z → α ⊑ z) (cong PFormula.pos pf≡notB) p))
                  ...   | there yInΓ' =
                      inr
                        (∈Init-++⁺ˡ
                          (pf ,
                            pf-keep
                              {x = (A ^ α)} {y = pf} {Γ = Γ'}
                              yInΓ' (λ q → y≠A (sym q)) ,
                            p))
              c-notl-gen D c₀ = tt
              c-notl-gen T c₀ = tt
              c-notl-gen D4 c₀ = tt
              c-notl-gen S4 c₀ = tt
              c-notl-gen S4dot2 c₀ = tt
              c-notl-gen S5 c₀ = tt

              c-notl :
                cutConstraint M A α Γl Γ' (((Not B' ^ β') ∷ Δl)) ((B ^ β) ∷ Δ')
              c-notl = c-notl-gen M c

              c-mix-B-gen :
                (m : Logic)
                → cutConstraint m A α Γl ((Not B ^ β) ∷ Γ') ((Not B' ^ β') ∷ Δl) Δ'
                → cutConstraint m B β
                    (Γl ++ (Γ' -pf (A ^ α)))
                    ((B ^ β) ∷ (Γl ++ (Γ' -pf (A ^ α))))
                    ((Δl -pf (A ^ α)) ++ (B ^ β) ∷ Δ')
                    ((Δl -pf (A ^ α)) ++ Δ')
              c-mix-B-gen K (inl w) = branchK-L wβ
                where
                  eqSuccL' :
                    ((Not B' ^ β') ∷ Δl) -pf (A ^ α)
                    ≡ (Δl -pf (A ^ α))
                  eqSuccL' =
                    pf-cons-eq {φ = (A ^ α)} {ψ = (Not B' ^ β')} {Γ = Δl} eq_left

                  α≡β : α ≡ β
                  α≡β = sym (pf-pos eq)

                  wα' : α ∈Init (Γl ++ (Δl -pf (A ^ α)))
                  wα' = subst (α ∈Init_) (cong (Γl ++_) eqSuccL') w

                  wβ : β ∈Init (Γl ++ (Δl -pf (A ^ α)))
                  wβ = subst (λ t → t ∈Init (Γl ++ (Δl -pf (A ^ α)))) α≡β wα'

                  branchK-L :
                    β ∈Init (Γl ++ (Δl -pf (A ^ α)))
                    → cutConstraint K B β
                        (Γl ++ (Γ' -pf (A ^ α)))
                        ((B ^ β) ∷ (Γl ++ (Γ' -pf (A ^ α))))
                        ((Δl -pf (A ^ α)) ++ (B ^ β) ∷ Δ')
                        ((Δl -pf (A ^ α)) ++ Δ')
                  branchK-L wL with ∈Init-++⁻ Γl wL
                  ... | inl wΓl =
                    inl (∈Init-++⁺ˡ (∈Init-++⁺ˡ wΓl))
                  ... | inr wΔl =
                    inr
                      (∈Init-++⁺ʳ
                        (((B ^ β) ∷ (Γl ++ (Γ' -pf (A ^ α)))) -pf (B ^ β))
                        (∈Init-++⁺ˡ wΔl))

              c-mix-B-gen K (inr w) = branchK-R wβ
                where
                  eqAntR' : ((Not B ^ β) ∷ Γ') -pf (A ^ α) ≡ (Γ' -pf (A ^ α))
                  eqAntR' =
                    pf-cons-eq-raw {φ = (A ^ α)} {ψ = (Not B ^ β)} {Γ = Γ'} (sym eq)

                  α≡β : α ≡ β
                  α≡β = sym (pf-pos eq)

                  wα' : α ∈Init ((Γ' -pf (A ^ α)) ++ Δ')
                  wα' = subst (α ∈Init_) (cong (_++ Δ') eqAntR') w

                  wβ : β ∈Init ((Γ' -pf (A ^ α)) ++ Δ')
                  wβ = subst (λ t → t ∈Init ((Γ' -pf (A ^ α)) ++ Δ')) α≡β wα'

                  branchK-R :
                    β ∈Init ((Γ' -pf (A ^ α)) ++ Δ')
                    → cutConstraint K B β
                        (Γl ++ (Γ' -pf (A ^ α)))
                        ((B ^ β) ∷ (Γl ++ (Γ' -pf (A ^ α))))
                        ((Δl -pf (A ^ α)) ++ (B ^ β) ∷ Δ')
                        ((Δl -pf (A ^ α)) ++ Δ')
                  branchK-R wR with ∈Init-++⁻ (Γ' -pf (A ^ α)) wR
                  ... | inl wΓ' =
                    inl (∈Init-++⁺ˡ (∈Init-++⁺ʳ Γl wΓ'))
                  ... | inr wΔ' =
                    inr
                      (∈Init-++⁺ʳ
                        (((B ^ β) ∷ (Γl ++ (Γ' -pf (A ^ α)))) -pf (B ^ β))
                        (∈Init-++⁺ʳ (Δl -pf (A ^ α)) wΔ'))

              c-mix-B-gen K4 (inl w) = branchK4-L wβ
                where
                  eqSuccL' :
                    ((Not B' ^ β') ∷ Δl) -pf (A ^ α)
                    ≡ (Δl -pf (A ^ α))
                  eqSuccL' =
                    pf-cons-eq {φ = (A ^ α)} {ψ = (Not B' ^ β')} {Γ = Δl} eq_left

                  α≡β : α ≡ β
                  α≡β = sym (pf-pos eq)

                  wα' : α ∈Init (Γl ++ (Δl -pf (A ^ α)))
                  wα' = subst (α ∈Init_) (cong (Γl ++_) eqSuccL') w

                  wβ : β ∈Init (Γl ++ (Δl -pf (A ^ α)))
                  wβ = subst (λ t → t ∈Init (Γl ++ (Δl -pf (A ^ α)))) α≡β wα'

                  branchK4-L :
                    β ∈Init (Γl ++ (Δl -pf (A ^ α)))
                    → cutConstraint K4 B β
                        (Γl ++ (Γ' -pf (A ^ α)))
                        ((B ^ β) ∷ (Γl ++ (Γ' -pf (A ^ α))))
                        ((Δl -pf (A ^ α)) ++ (B ^ β) ∷ Δ')
                        ((Δl -pf (A ^ α)) ++ Δ')
                  branchK4-L wL with ∈Init-++⁻ Γl wL
                  ... | inl wΓl =
                    inl (∈Init-++⁺ˡ (∈Init-++⁺ˡ wΓl))
                  ... | inr wΔl =
                    inr
                      (∈Init-++⁺ʳ
                        (((B ^ β) ∷ (Γl ++ (Γ' -pf (A ^ α)))) -pf (B ^ β))
                        (∈Init-++⁺ˡ wΔl))

              c-mix-B-gen K4 (inr w) = branchK4-R wβ
                where
                  eqAntR' : ((Not B ^ β) ∷ Γ') -pf (A ^ α) ≡ (Γ' -pf (A ^ α))
                  eqAntR' =
                    pf-cons-eq-raw {φ = (A ^ α)} {ψ = (Not B ^ β)} {Γ = Γ'} (sym eq)

                  α≡β : α ≡ β
                  α≡β = sym (pf-pos eq)

                  wα' : α ∈Init ((Γ' -pf (A ^ α)) ++ Δ')
                  wα' = subst (α ∈Init_) (cong (_++ Δ') eqAntR') w

                  wβ : β ∈Init ((Γ' -pf (A ^ α)) ++ Δ')
                  wβ = subst (λ t → t ∈Init ((Γ' -pf (A ^ α)) ++ Δ')) α≡β wα'

                  branchK4-R :
                    β ∈Init ((Γ' -pf (A ^ α)) ++ Δ')
                    → cutConstraint K4 B β
                        (Γl ++ (Γ' -pf (A ^ α)))
                        ((B ^ β) ∷ (Γl ++ (Γ' -pf (A ^ α))))
                        ((Δl -pf (A ^ α)) ++ (B ^ β) ∷ Δ')
                        ((Δl -pf (A ^ α)) ++ Δ')
                  branchK4-R wR with ∈Init-++⁻ (Γ' -pf (A ^ α)) wR
                  ... | inl wΓ' =
                    inl (∈Init-++⁺ˡ (∈Init-++⁺ʳ Γl wΓ'))
                  ... | inr wΔ' =
                    inr
                      (∈Init-++⁺ʳ
                        (((B ^ β) ∷ (Γl ++ (Γ' -pf (A ^ α)))) -pf (B ^ β))
                        (∈Init-++⁺ʳ (Δl -pf (A ^ α)) wΔ'))

              c-mix-B-gen D c₀ = tt
              c-mix-B-gen T c₀ = tt
              c-mix-B-gen D4 c₀ = tt
              c-mix-B-gen S4 c₀ = tt
              c-mix-B-gen S4dot2 c₀ = tt
              c-mix-B-gen S5 c₀ = tt

              c-mix-B :
                cutConstraint M B β
                  (Γl ++ (Γ' -pf (A ^ α)))
                  ((B ^ β) ∷ (Γl ++ (Γ' -pf (A ^ α))))
                  ((Δl -pf (A ^ α)) ++ (B ^ β) ∷ Δ')
                  ((Δl -pf (A ^ α)) ++ Δ')
              c-mix-B = c-mix-B-gen M c
          notLCase Π rec' (yes eq) = mixGo Π (NotL {A = B} {α = β} Πsub) c (acc rec')
          notLCase Π rec' (no not≢a)
            with cutConstraint-down-right-NotL
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {α = α} {β = β} c
          ... | just c↓ =
            mix-lift-right-NotL
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {α = α} {β = β}
              not≢a (max (δ Π) (δ Πsub))
              (mixGo {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ'} {Δ₀' = (B ^ β) ∷ Δ'}
                Π Πsub c↓
                (rec' _ (step-lex-height (step-right-+1 (height Π) (height Πsub)))))
          ... | nothing = mixGo Π (NotL {A = B} {α = β} Πsub) c (acc rec')
      mixGoR {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ'} {Δ₀' = (Not B ^ β) ∷ Δ'}
        Π₀ (NotR {A = B} {α = β} Πsub) c (acc rec) =
        notRCase ((Not B ^ β) ≟pf (A ^ α))
        where
          notRCase : Dec ((Not B ^ β) ≡ (A ^ α))
            → MixResult (max (δ Π₀) (δ Πsub))
                {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = (Not B ^ β) ∷ Δ'} {A = A} {α = α}
          notRCase (yes eq)
            with cutConstraint-down-right-NotR
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {α = α} {β = β} c
          ... | just c↓ =
            let
              b≢a : Neg ((B ^ β) ≡ (A ^ α))
              b≢a p = Cubical.Data.Nat.Order.¬m<m
                (subst (degree B <_)
                  (sym (cong degree (pf-form (p ∙ sym eq))))
                  degree-sub-Not)

              (Πcross , dcross) =
                mixGo {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (B ^ β) ∷ Γ'} {Δ₀' = Δ'}
                  Π₀ Πsub c↓
                  (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub))))

              eqAnt : (((B ^ β) ∷ Γ') -pf (A ^ α))
                   ≡ ((B ^ β) ∷ (Γ' -pf (A ^ α)))
              eqAnt =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'}
                  (λ q → b≢a (sym q))

              eqAntCtx = cong (Γ ++_) eqAnt
              rhs = (Δ -pf (A ^ α)) ++ Δ'
              lhs = Γ ++ (Γ' -pf (A ^ α))

              (Πmid , dmid) = subst-δ-Γ eqAntCtx Πcross dcross

              subL = subset-append-mid-cons Γ (Γ' -pf (A ^ α)) (B ^ β)
              (Πprem , dprem) = structural-δ subL subset-refl Πmid dmid

              Πnot = NotR Πprem

              subD = subset-cons-append-mid (Δ -pf (A ^ α)) Δ' (Not B ^ β)
              (Πres , dres) = structural-δ subset-refl subD Πnot dprem
            in Πres , dres
          ... | nothing = mixGo Π₀ (NotR {A = B} {α = β} Πsub) c (acc rec)
          notRCase (no not≢a)
            with cutConstraint-down-right-NotR
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {α = α} {β = β} c
          ... | just c↓ =
            mix-lift-right-NotR
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {α = α} {β = β}
              not≢a (max (δ Π₀) (δ Πsub))
              (mixGo {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (B ^ β) ∷ Γ'} {Δ₀' = Δ'}
                Π₀ Πsub c↓
                (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))
          ... | nothing = mixGo Π₀ (NotR {A = B} {α = β} Πsub) c (acc rec)
      mixGoR {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (And B C ^ β) ∷ Γ'} {Δ₀' = Δ'}
        Π₀ (AndL1 {B = C} Πsub) c (acc rec) =
        andL1Case Π₀ rec ((And B C ^ β) ≟pf (A ^ α))
        where
          andL1Case : (Π : Γ ⊢ Δ)
            → (∀ m → m <Lex (n , mixHeight Π (AndL1 {A = B} {B = C} Πsub)) → Acc _<Lex_ m)
            → Dec ((And B C ^ β) ≡ (A ^ α))
            → MixResult (max (δ Π) (δ Πsub))
                {Γ = Γ} {Δ = Δ} {Γ' = (And B C ^ β) ∷ Γ'} {Δ' = Δ'} {A = A} {α = α}
          andL1Case (AndR {Γ₁ = Γl₁} {A = B'} {α = β'} {Δ₁ = Δl₁}
                           {Γ₂ = Γl₂} {B = C'} {Δ₂ = Δl₂}
                           Πsub-l₁ Πsub-l₂) rec' (yes eq)
            with (And B' C' ^ β') ≟pf (A ^ α)
          ... | no and'≢a =
            let
              eqSuccPr :
                ((And B' C' ^ β') ∷ (Δl₁ ++ Δl₂)) -pf (A ^ α)
                ≡ (And B' C' ^ β') ∷ ((Δl₁ ++ Δl₂) -pf (A ^ α))
              eqSuccPr =
                pf-cons-neq {φ = (A ^ α)} {ψ = (And B' C' ^ β')} {Γ = Δl₁ ++ Δl₂}
                  (λ q → and'≢a (sym q))
              (res-pr , d-res-pr) =
                mixGo (AndR Πsub-l₁ Πsub-l₂) (AndL1 {A = B} {B = C} Πsub) c (acc rec')
              (res-pr' , d-res-pr') =
                subst-δ-Δ (cong (_++ Δ') eqSuccPr) res-pr d-res-pr
            in (res-pr' , d-res-pr')
          ... | yes eq_left =
            let
              and-eq : (And B' C' ^ β') ≡ (And B C ^ β)
              and-eq = eq_left ∙ sym eq

              B-eq : B' ≡ B
              B-eq = And-inj-l (pf-form and-eq)

              C-eq : C' ≡ C
              C-eq = And-inj-r (pf-form and-eq)

              β-eq : β' ≡ β
              β-eq = pf-pos and-eq

              Bt-eq : (B' ^ β') ≡ (B ^ β)
              Bt-eq = cong₂ _^_ B-eq β-eq

              degB<n : degree B < n
              degB<n =
                subst (degree B <_) (cong degree (pf-form eq) ∙ degEq) degree-sub-AndL
              eqSuccPr :
                ((And B' C' ^ β') ∷ (Δl₁ ++ Δl₂)) -pf (A ^ α)
                ≡ ((Δl₁ ++ Δl₂) -pf (A ^ α))
              eqSuccPr =
                pf-cons-eq {φ = (A ^ α)} {ψ = (And B' C' ^ β')} {Γ = Δl₁ ++ Δl₂} eq_left
              (res-pr , d-res-pr) =
                mixGo (AndR Πsub-l₁ Πsub-l₂) (AndL1 {A = B} {B = C} Πsub) c (acc rec')
              (res-pr' , d-res-pr') = subst-δ-Δ (cong (_++ Δ') eqSuccPr) res-pr d-res-pr
            in (res-pr' , d-res-pr')
          andL1Case Π rec' (yes eq) = mixGo Π (AndL1 {A = B} {B = C} Πsub) c (acc rec')
          andL1Case Π rec' (no and≢a)
            with cutConstraint-down-right-AndL1
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c↓ =
            mix-lift-right-AndL1
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {C = C} {α = α} {β = β}
              and≢a (max (δ Π) (δ Πsub))
              (mixGo {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (B ^ β) ∷ Γ'} {Δ₀' = Δ'}
                Π Πsub c↓
                (rec' _ (step-lex-height (step-right-+1 (height Π) (height Πsub)))))
          ... | nothing = mixGo Π (AndL1 {B = C} Πsub) c (acc rec')
      mixGoR {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (And B C ^ β) ∷ Γ'} {Δ₀' = Δ'}
        Π₀ (AndL2 {A = B} Πsub) c (acc rec) =
        andL2Case Π₀ rec ((And B C ^ β) ≟pf (A ^ α))
        where
          andL2Case : (Π : Γ ⊢ Δ)
            → (∀ m → m <Lex (n , mixHeight Π (AndL2 {A = B} Πsub)) → Acc _<Lex_ m)
            → Dec ((And B C ^ β) ≡ (A ^ α))
            → MixResult (max (δ Π) (δ Πsub))
                {Γ = Γ} {Δ = Δ} {Γ' = (And B C ^ β) ∷ Γ'} {Δ' = Δ'} {A = A} {α = α}
          andL2Case (AndR {Γ₁ = Γl₁} {A = B'} {α = β'} {Δ₁ = Δl₁}
                           {Γ₂ = Γl₂} {B = C'} {Δ₂ = Δl₂}
                           Πsub-l₁ Πsub-l₂) rec' (yes eq)
            with (And B' C' ^ β') ≟pf (A ^ α)
          ... | no and'≢a =
            let
              eqSuccPr :
                ((And B' C' ^ β') ∷ (Δl₁ ++ Δl₂)) -pf (A ^ α)
                ≡ (And B' C' ^ β') ∷ ((Δl₁ ++ Δl₂) -pf (A ^ α))
              eqSuccPr =
                pf-cons-neq {φ = (A ^ α)} {ψ = (And B' C' ^ β')} {Γ = Δl₁ ++ Δl₂}
                  (λ q → and'≢a (sym q))
              (res-pr , d-res-pr) =
                mixGo (AndR Πsub-l₁ Πsub-l₂) (AndL2 {A = B} Πsub) c (acc rec')
              (res-pr' , d-res-pr') =
                subst-δ-Δ (cong (_++ Δ') eqSuccPr) res-pr d-res-pr
            in (res-pr' , d-res-pr')
          ... | yes eq_left =
            let
              and-eq : (And B' C' ^ β') ≡ (And B C ^ β)
              and-eq = eq_left ∙ sym eq

              B-eq : B' ≡ B
              B-eq = And-inj-l (pf-form and-eq)

              C-eq : C' ≡ C
              C-eq = And-inj-r (pf-form and-eq)

              β-eq : β' ≡ β
              β-eq = pf-pos and-eq

              Ct-eq : (C' ^ β') ≡ (C ^ β)
              Ct-eq = cong₂ _^_ C-eq β-eq

              degC<n : degree C < n
              degC<n =
                subst (degree C <_) (cong degree (pf-form eq) ∙ degEq)
                  (degree-sub-AndR {A = B} {B = C})
              eqSuccPr :
                ((And B' C' ^ β') ∷ (Δl₁ ++ Δl₂)) -pf (A ^ α)
                ≡ ((Δl₁ ++ Δl₂) -pf (A ^ α))
              eqSuccPr =
                pf-cons-eq {φ = (A ^ α)} {ψ = (And B' C' ^ β')} {Γ = Δl₁ ++ Δl₂} eq_left
              (res-pr , d-res-pr) =
                mixGo (AndR Πsub-l₁ Πsub-l₂) (AndL2 {A = B} Πsub) c (acc rec')
              (res-pr' , d-res-pr') = subst-δ-Δ (cong (_++ Δ') eqSuccPr) res-pr d-res-pr
            in (res-pr' , d-res-pr')
          andL2Case Π rec' (yes eq) = mixGo Π (AndL2 {A = B} Πsub) c (acc rec')
          andL2Case Π rec' (no and≢a)
            with cutConstraint-down-right-AndL2
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c↓ =
            mix-lift-right-AndL2
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {C = C} {α = α} {β = β}
              and≢a (max (δ Π) (δ Πsub))
              (mixGo {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (C ^ β) ∷ Γ'} {Δ₀' = Δ'}
                Π Πsub c↓
                (rec' _ (step-lex-height (step-right-+1 (height Π) (height Πsub)))))
          ... | nothing = mixGo Π (AndL2 {A = B} Πsub) c (acc rec')
      mixGoR {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ'} {Δ₀' = (Or B C ^ β) ∷ Δ'}
        Π₀ (OrR1 {A = B} {α = β} {B = C} Πsub) c (acc rec)
        with cutConstraint-down-right-OrR1
          {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
          {A = A} {B = B} {C = C} {α = α} {β = β} c
      ... | just c↓ =
        mix-lift-right-OrR1
          {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
          {A = A} {B = B} {C = C} {α = α} {β = β}
          (max (δ Π₀) (δ Πsub))
          (mixGo {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ'} {Δ₀' = (B ^ β) ∷ Δ'}
            Π₀ Πsub c↓
            (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))
      ... | nothing = mixGo Π₀ (OrR1 {A = B} {α = β} {B = C} Πsub) c (acc rec)
      mixGoR {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ'} {Δ₀' = (Or B C ^ β) ∷ Δ'}
        Π₀ (OrR2 {A = B} Πsub) c (acc rec)
        with cutConstraint-down-right-OrR2
          {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
          {A = A} {B = B} {C = C} {α = α} {β = β} c
      ... | just c↓ =
        mix-lift-right-OrR2
          {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
          {A = A} {B = B} {C = C} {α = α} {β = β}
          (max (δ Π₀) (δ Πsub))
          (mixGo {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ'} {Δ₀' = (C ^ β) ∷ Δ'}
            Π₀ Πsub c↓
            (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))
      ... | nothing = mixGo Π₀ (OrR2 {A = B} Πsub) c (acc rec)
      mixGoR {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ'} {Δ₀' = ((B ⇒ C) ^ β) ∷ Δ'}
        Π₀ (ImpR {A = B} {α = β} {B = C} Πsub) c (acc rec) =
        impCase (((B ⇒ C) ^ β) ≟pf (A ^ α))
        where
          impCase : Dec (((B ⇒ C) ^ β) ≡ (A ^ α))
            → MixResult (max (δ Π₀) (δ Πsub))
                {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = ((B ⇒ C) ^ β) ∷ Δ'} {A = A} {α = α}
          impCase (yes eq)
            with cutConstraint-down-right-ImpR
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c↓ =
            let
              b≢a : Neg ((B ^ β) ≡ (A ^ α))
              b≢a p = Cubical.Data.Nat.Order.¬m<m
                (subst (degree B <_)
                  (sym (cong degree (pf-form (p ∙ sym eq))))
                  degree-sub-ImpL)

              (Πcross , dcross) =
                mixGo {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (B ^ β) ∷ Γ'} {Δ₀' = (C ^ β) ∷ Δ'}
                  Π₀ Πsub c↓
                  (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub))))

              rem = Γ' -pf (A ^ α)

              eqAnt : (((B ^ β) ∷ Γ') -pf (A ^ α))
                   ≡ ((B ^ β) ∷ rem)
              eqAnt =
                pf-cons-neq
                  {φ = (A ^ α)} {ψ = (B ^ β)} {Γ = Γ'}
                  (λ q → b≢a (sym q))

              eqAntCtx = cong (Γ ++_) eqAnt
              rhs₀ = (Δ -pf (A ^ α)) ++ ((C ^ β) ∷ Δ')
              lhs = Γ ++ rem

              (Πmid , dmid) = subst-δ-Γ eqAntCtx Πcross dcross

              subL = subset-append-mid-cons Γ rem (B ^ β)
              (ΠL , dΠL) = structural-δ subL subset-refl Πmid dmid

              subD₁ = subset-append-mid-cons (Δ -pf (A ^ α)) Δ' (C ^ β)
              (Πprem , dprem) = structural-δ subset-refl subD₁ ΠL dΠL

              Πimp = ImpR Πprem

              subD₂ = subset-cons-append-mid (Δ -pf (A ^ α)) Δ' ((B ⇒ C) ^ β)
              (Πres , dres) = structural-δ subset-refl subD₂ Πimp dprem
            in Πres , dres
          ... | nothing = mixGo Π₀ (ImpR {A = B} {α = β} {B = C} Πsub) c (acc rec)
          impCase (no imp≢a)
            with cutConstraint-down-right-ImpR
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c↓ =
            mix-lift-right-ImpR
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {C = C} {α = α} {β = β}
              imp≢a (max (δ Π₀) (δ Πsub))
              (mixGo {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (B ^ β) ∷ Γ'} {Δ₀' = (C ^ β) ∷ Δ'}
                Π₀ Πsub c↓
                (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))
          ... | nothing = mixGo Π₀ (ImpR {A = B} {α = β} {B = C} Πsub) c (acc rec)
      -- Binary right
      mixGoR
        {Γ₀ = Γ} {Δ₀ = Δ}
        Π₀
        (AndR {Γ₁ = Γ₁'} {A = B} {α = β} {Δ₁ = Δ₁'}
              {Γ₂ = Γ₂'} {B = C} {Δ₂ = Δ₂'} Π₁ Π₂)
        c (acc rec)
        with cutConstraint-down-right-AndR₁
          {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Δ₁' = Δ₁'} {Γ₂' = Γ₂'} {Δ₂' = Δ₂'}
          {A = A} {B = B} {C = C} {α = α} {β = β} c
           | cutConstraint-down-right-AndR₂
          {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Δ₁' = Δ₁'} {Γ₂' = Γ₂'} {Δ₂' = Δ₂'}
          {A = A} {B = B} {C = C} {α = α} {β = β} c
      ... | just c₁ | just c₂ =
        mix-lift-right-AndR
          {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Γ₂' = Γ₂'} {Δ₁' = Δ₁'} {Δ₂' = Δ₂'}
          {A = A} {B = B} {C = C} {α = α} {β = β}
          (max (δ Π₀) (max (δ Π₁) (δ Π₂)))
          (liftMixResult
            {m = max (δ Π₀) (δ Π₁)}
            {n = max (δ Π₀) (max (δ Π₁) (δ Π₂))}
            {Γ = Γ} {Δ = Δ} {Γ' = Γ₁'} {Δ' = (B ^ β) ∷ Δ₁'} {A = A} {α = α}
            (max-least
              (left-≤-max {m = δ Π₀} {n = max (δ Π₁) (δ Π₂)})
              (≤-trans
                (left-≤-max {m = δ Π₁} {n = δ Π₂})
                (right-≤-max {n = max (δ Π₁) (δ Π₂)} {m = δ Π₀})))
            (mixGo
              {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ₁'} {Δ₀' = (B ^ β) ∷ Δ₁'}
              Π₀ Π₁ c₁
              (rec _ (step-lex-height (step-right-binary₁ (height Π₁) (height Π₂) (height Π₀))))))
          (liftMixResult
            {m = max (δ Π₀) (δ Π₂)}
            {n = max (δ Π₀) (max (δ Π₁) (δ Π₂))}
            {Γ = Γ} {Δ = Δ} {Γ' = Γ₂'} {Δ' = (C ^ β) ∷ Δ₂'} {A = A} {α = α}
            (max-least
              (left-≤-max {m = δ Π₀} {n = max (δ Π₁) (δ Π₂)})
              (≤-trans
                (right-≤-max {n = δ Π₂} {m = δ Π₁})
                (right-≤-max {n = max (δ Π₁) (δ Π₂)} {m = δ Π₀})))
            (mixGo
              {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ₂'} {Δ₀' = (C ^ β) ∷ Δ₂'}
              Π₀ Π₂ c₂
              (rec _ (step-lex-height (step-right-binary₂ (height Π₁) (height Π₂) (height Π₀))))))
      ... | _ | _ = mixGo Π₀ (AndR Π₁ Π₂) c (acc rec)
      mixGoR
        {Γ₀ = Γ} {Δ₀ = Δ}
        Π₀
        (OrL {A = B} {α = β} {Γ₁ = Γ₁'} {Δ₁ = Δ₁'}
             {B = C} {Γ₂ = Γ₂'} {Δ₂ = Δ₂'} Π₁ Π₂)
        c (acc rec) =
        orLCase Π₀ rec ((Or B C ^ β) ≟pf (A ^ α))
        where
          orLCase : (Π : Γ ⊢ Δ)
            → (∀ m → m <Lex (n , mixHeight Π (OrL Π₁ Π₂)) → Acc _<Lex_ m)
            → Dec ((Or B C ^ β) ≡ (A ^ α))
            → MixResult (max (δ Π) (max (δ Π₁) (δ Π₂)))
                {Γ = Γ} {Δ = Δ}
                {Γ' = (Or B C ^ β) ∷ (Γ₁' ++ Γ₂')} {Δ' = Δ₁' ++ Δ₂'}
                {A = A} {α = α}
          orLCase (OrR1 {A = B'} {α = β'} {B = C'} Πsub-l) rec' (yes eq)
            with (Or B' C' ^ β') ≟pf (A ^ α)
          ... | no or'≢a =
            let
              (res-pr , d-res-pr) =
                mixGo (OrR1 {A = B'} {α = β'} {B = C'} Πsub-l) (OrL Π₁ Π₂) c (acc rec')
              (res-pr' , d-res-pr') =
                subst-δ-Δ
                  (cong (_++ (Δ₁' ++ Δ₂'))
                    (pf-cons-neq {φ = (A ^ α)} {ψ = (Or B' C' ^ β')} {Γ = _}
                      (λ q → or'≢a (sym q))))
                  res-pr d-res-pr
            in (res-pr' , d-res-pr')
          ... | yes eq_left =
            let
              (res-pr , d-res-pr) =
                mixGo (OrR1 {A = B'} {α = β'} {B = C'} Πsub-l) (OrL Π₁ Π₂) c (acc rec')
              (res-pr' , d-res-pr') =
                subst-δ-Δ
                  (cong (_++ (Δ₁' ++ Δ₂'))
                    (pf-cons-eq {φ = (A ^ α)} {ψ = (Or B' C' ^ β')} {Γ = _} eq_left))
                  res-pr d-res-pr
            in (res-pr' , d-res-pr')

          orLCase (OrR2 {A = B'} Πsub-l) rec' (yes eq) =
            let
              (res-pr , d-res-pr) =
                mixGo (OrR2 {A = B'} Πsub-l) (OrL Π₁ Π₂) c (acc rec')
            in (res-pr , d-res-pr)

          orLCase Π rec' (yes eq) = mixGo Π (OrL Π₁ Π₂) c (acc rec')
          orLCase Π rec' (no or≢a)
            with cutConstraint-down-right-OrL₁
              {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Δ₁' = Δ₁'} {Γ₂' = Γ₂'} {Δ₂' = Δ₂'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
               | cutConstraint-down-right-OrL₂
              {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Δ₁' = Δ₁'} {Γ₂' = Γ₂'} {Δ₂' = Δ₂'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c₁ | just c₂ =
            mix-lift-right-OrL
              {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Γ₂' = Γ₂'} {Δ₁' = Δ₁'} {Δ₂' = Δ₂'}
              {A = A} {B = B} {C = C} {α = α} {β = β}
              or≢a (max (δ Π) (max (δ Π₁) (δ Π₂)))
              (liftMixResult
                {m = max (δ Π) (δ Π₁)}
                {n = max (δ Π) (max (δ Π₁) (δ Π₂))}
                {Γ = Γ} {Δ = Δ} {Γ' = (B ^ β) ∷ Γ₁'} {Δ' = Δ₁'} {A = A} {α = α}
                (max-least
                  (left-≤-max {m = δ Π} {n = max (δ Π₁) (δ Π₂)})
                  (≤-trans
                    (left-≤-max {m = δ Π₁} {n = δ Π₂})
                    (right-≤-max {n = max (δ Π₁) (δ Π₂)} {m = δ Π})))
                (mixGo
                  {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (B ^ β) ∷ Γ₁'} {Δ₀' = Δ₁'}
                  Π Π₁ c₁
                  (rec' _ (step-lex-height (step-right-binary₁ (height Π₁) (height Π₂) (height Π))))))
              (liftMixResult
                {m = max (δ Π) (δ Π₂)}
                {n = max (δ Π) (max (δ Π₁) (δ Π₂))}
                {Γ = Γ} {Δ = Δ} {Γ' = (C ^ β) ∷ Γ₂'} {Δ' = Δ₂'} {A = A} {α = α}
                (max-least
                  (left-≤-max {m = δ Π} {n = max (δ Π₁) (δ Π₂)})
                  (≤-trans
                    (right-≤-max {n = δ Π₂} {m = δ Π₁})
                    (right-≤-max {n = max (δ Π₁) (δ Π₂)} {m = δ Π})))
                (mixGo
                  {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (C ^ β) ∷ Γ₂'} {Δ₀' = Δ₂'}
                  Π Π₂ c₂
                  (rec' _ (step-lex-height (step-right-binary₂ (height Π₁) (height Π₂) (height Π))))))
          ... | _ | _ = mixGo Π (OrL {A = B} {α = β} {Γ₁ = Γ₁'} {Δ₁ = Δ₁'}
            {B = C} {Γ₂ = Γ₂'} {Δ₂ = Δ₂'} Π₁ Π₂) c (acc rec')
      mixGoR
        {Γ₀ = Γ} {Δ₀ = Δ}
        Π₀
        (ImpL {Γ₁ = Γ₁'} {A = B} {α = β} {Δ₁ = Δ₁'}
              {B = C} {Γ₂ = Γ₂'} {Δ₂ = Δ₂'} Π₁ Π₂)
        c (acc rec) =
        impLCase Π₀ rec (((B ⇒ C) ^ β) ≟pf (A ^ α))
        where
          impLCase : (Π : Γ ⊢ Δ)
            → (∀ m → m <Lex (n , mixHeight Π (ImpL Π₁ Π₂)) → Acc _<Lex_ m)
            → Dec (((B ⇒ C) ^ β) ≡ (A ^ α))
            → MixResult (max (δ Π) (max (δ Π₁) (δ Π₂)))
                {Γ = Γ} {Δ = Δ}
                {Γ' = ((B ⇒ C) ^ β) ∷ (Γ₁' ++ Γ₂')} {Δ' = Δ₁' ++ Δ₂'}
                {A = A} {α = α}
          impLCase (ImpR {A = B'} {α = β'} {B = C'} {Δ = Δl} Πsub-l) rec' (yes eq)
            with ((B' ⇒ C') ^ β') ≟pf (A ^ α)
          ... | no imp'≢a =
            let
              eqSuccPr :
                (((B' ⇒ C') ^ β') ∷ Δl) -pf (A ^ α)
                ≡ (((B' ⇒ C') ^ β') ∷ (Δl -pf (A ^ α)))
              eqSuccPr =
                pf-cons-neq {φ = (A ^ α)} {ψ = ((B' ⇒ C') ^ β')} {Γ = Δl}
                  (λ q → imp'≢a (sym q))
              (res-pr , d-res-pr) =
                mixGo (ImpR {A = B'} {α = β'} {B = C'} Πsub-l)
                      (ImpL {Γ₁ = Γ₁'} {A = B} {α = β} {Δ₁ = Δ₁'} {B = C} {Γ₂ = Γ₂'} {Δ₂ = Δ₂'} Π₁ Π₂)
                      c (acc rec')
              (res-pr' , d-res-pr') =
                subst-δ-Δ (cong (_++ (Δ₁' ++ Δ₂')) eqSuccPr) res-pr d-res-pr
            in (res-pr' , d-res-pr')
          ... | yes eq_left =
            let
              imp-eq : ((B' ⇒ C') ^ β') ≡ ((B ⇒ C) ^ β)
              imp-eq = eq_left ∙ sym eq

              B-eq : B' ≡ B
              B-eq = Imp-inj-l (pf-form imp-eq)

              C-eq : C' ≡ C
              C-eq = Imp-inj-r (pf-form imp-eq)

              β-eq : β' ≡ β
              β-eq = pf-pos imp-eq

              degB<n : degree B < n
              degB<n = subst (degree B <_) (cong degree (pf-form eq) ∙ degEq) degree-sub-ImpL
              eqSuccPr :
                (((B' ⇒ C') ^ β') ∷ Δl) -pf (A ^ α)
                ≡ (Δl -pf (A ^ α))
              eqSuccPr =
                pf-cons-eq {φ = (A ^ α)} {ψ = ((B' ⇒ C') ^ β')} {Γ = Δl} eq_left

              (res-pr , d-res-pr) =
                mixGo (ImpR {A = B'} {α = β'} {B = C'} {Δ = Δl} Πsub-l)
                      (ImpL {Γ₁ = Γ₁'} {A = B} {α = β} {Δ₁ = Δ₁'} {B = C} {Γ₂ = Γ₂'} {Δ₂ = Δ₂'} Π₁ Π₂)
                      c (acc rec')
              (res-pr' , d-res-pr') =
                subst-δ-Δ (cong (_++ (Δ₁' ++ Δ₂')) eqSuccPr) res-pr d-res-pr
            in (res-pr' , d-res-pr')
          impLCase Π rec' (yes eq) = mixGo Π (ImpL {Γ₁ = Γ₁'} {A = B} {α = β} {Δ₁ = Δ₁'}
            {B = C} {Γ₂ = Γ₂'} {Δ₂ = Δ₂'} Π₁ Π₂) c (acc rec')
          impLCase Π rec' (no imp≢a)
            with cutConstraint-down-right-ImpL₁
              {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Δ₁' = Δ₁'} {Γ₂' = Γ₂'} {Δ₂' = Δ₂'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
               | cutConstraint-down-right-ImpL₂
              {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Δ₁' = Δ₁'} {Γ₂' = Γ₂'} {Δ₂' = Δ₂'}
              {A = A} {B = B} {C = C} {α = α} {β = β} c
          ... | just c₁ | just c₂ =
            mix-lift-right-ImpL
              {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Γ₂' = Γ₂'} {Δ₁' = Δ₁'} {Δ₂' = Δ₂'}
              {A = A} {B = B} {C = C} {α = α} {β = β}
              imp≢a (max (δ Π) (max (δ Π₁) (δ Π₂)))
              (liftMixResult
                {m = max (δ Π) (δ Π₁)}
                {n = max (δ Π) (max (δ Π₁) (δ Π₂))}
                {Γ = Γ} {Δ = Δ} {Γ' = Γ₁'} {Δ' = (B ^ β) ∷ Δ₁'} {A = A} {α = α}
                (max-least
                  (left-≤-max {m = δ Π} {n = max (δ Π₁) (δ Π₂)})
                  (≤-trans
                    (left-≤-max {m = δ Π₁} {n = δ Π₂})
                    (right-≤-max {n = max (δ Π₁) (δ Π₂)} {m = δ Π})))
                (mixGo
                  {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ₁'} {Δ₀' = (B ^ β) ∷ Δ₁'}
                  Π Π₁ c₁
                  (rec' _ (step-lex-height (step-right-binary₁ (height Π₁) (height Π₂) (height Π))))))
              (liftMixResult
                {m = max (δ Π) (δ Π₂)}
                {n = max (δ Π) (max (δ Π₁) (δ Π₂))}
                {Γ = Γ} {Δ = Δ} {Γ' = (C ^ β) ∷ Γ₂'} {Δ' = Δ₂'} {A = A} {α = α}
                (max-least
                  (left-≤-max {m = δ Π} {n = max (δ Π₁) (δ Π₂)})
                  (≤-trans
                    (right-≤-max {n = δ Π₂} {m = δ Π₁})
                    (right-≤-max {n = max (δ Π₁) (δ Π₂)} {m = δ Π})))
                (mixGo
                  {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = (C ^ β) ∷ Γ₂'} {Δ₀' = Δ₂'}
                  Π Π₂ c₂
                  (rec' _ (step-lex-height (step-right-binary₂ (height Π₁) (height Π₂) (height Π))))))
          ... | _ | _ = mixGo Π (ImpL {Γ₁ = Γ₁'} {A = B} {α = β} {Δ₁ = Δ₁'}
            {B = C} {Γ₂ = Γ₂'} {Δ₂ = Δ₂'} Π₁ Π₂) c (acc rec')
      -- Cut on right
      mixGoR
        {Γ₀ = Γ} {Δ₀ = Δ}
        Π₀
        (Cut {A = A'} {α = α'} {Γ₁ = Γ₁'} {Γ₂ = Γ₂'} {Δ₁ = Δ₁'} {Δ₂ = Δ₂'} cCut Π₁ Π₂)
        c (acc rec)
        with cutConstraint-down-right-Cut₁
          {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Δ₁' = Δ₁'} {Γ₂' = Γ₂'} {Δ₂' = Δ₂'}
          {A = A} {A' = A'} {α = α} {α' = α'} c
           | cutConstraint-down-right-Cut₂
          {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Δ₁' = Δ₁'} {Γ₂' = Γ₂'} {Δ₂' = Δ₂'}
          {A = A} {A' = A'} {α = α} {α' = α'} c
           | cutConstraint-rebuild
          {A = A'} {α = α'}
          {Γ₁ = Γ₁'} {Γ₂ = Γ₂'}
          {Δ₁ = Δ₁'} {Δ₂ = Δ₂'}
          {Γ₁' = Γ ++ (Γ₁' -pf (A ^ α))}
          {Γ₂' = Γ ++ (Γ₂' -pf (A ^ α))}
          {Δ₁' = (Δ -pf (A ^ α)) ++ Δ₁'}
          {Δ₂' = (Δ -pf (A ^ α)) ++ Δ₂'}
          cCut
      ... | just c₁ | just c₂ | just cCut' =
        cutCase ((A' ^ α') ≟pf (A ^ α))
        where
          nCut : ℕ
          nCut = max (δ Π₀) (max (suc (degree A')) (max (δ Π₁) (δ Π₂)))

          dA'≤nCut : suc (degree A') ≤ nCut
          dA'≤nCut =
            ≤-trans
              (left-≤-max {m = suc (degree A')} {n = max (δ Π₁) (δ Π₂)})
              (right-≤-max {n = max (suc (degree A')) (max (δ Π₁) (δ Π₂))} {m = δ Π₀})

          r₁ : Σ ((Γ ++ (Γ₁' -pf (A ^ α))) ⊢ ((Δ -pf (A ^ α)) ++ [ (A' ^ α') ] ++ Δ₁'))
               (λ Π₃ → δ Π₃ ≤ nCut)
          r₁ =
            liftMixResult
              {m = max (δ Π₀) (δ Π₁)}
              {n = nCut}
              {Γ = Γ} {Δ = Δ} {Γ' = Γ₁'} {Δ' = [ (A' ^ α') ] ++ Δ₁'} {A = A} {α = α}
              (max-least
                (left-≤-max {m = δ Π₀} {n = max (suc (degree A')) (max (δ Π₁) (δ Π₂))})
                (≤-trans
                  (left-≤-max {m = δ Π₁} {n = δ Π₂})
                  (≤-trans
                    (right-≤-max {n = max (δ Π₁) (δ Π₂)} {m = suc (degree A')})
                    (right-≤-max {n = max (suc (degree A')) (max (δ Π₁) (δ Π₂))} {m = δ Π₀}))))
              (mixGo
                {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ₁'} {Δ₀' = [ (A' ^ α') ] ++ Δ₁'}
                Π₀ Π₁ c₁
                (rec _ (step-lex-height (step-right-binary₁ (height Π₁) (height Π₂) (height Π₀)))))

          rhs₂ : Ctx
          rhs₂ = (Δ -pf (A ^ α)) ++ Δ₂'

          r₂raw : Σ ((Γ ++ ((Γ₂' ++ [ (A' ^ α') ]) -pf (A ^ α))) ⊢ rhs₂)
                  (λ Π₃ → δ Π₃ ≤ nCut)
          r₂raw =
            liftMixResult
              {m = max (δ Π₀) (δ Π₂)}
              {n = nCut}
              {Γ = Γ} {Δ = Δ} {Γ' = Γ₂' ++ [ (A' ^ α') ]} {Δ' = Δ₂'} {A = A} {α = α}
              (max-least
                (left-≤-max {m = δ Π₀} {n = max (suc (degree A')) (max (δ Π₁) (δ Π₂))})
                (≤-trans
                  (right-≤-max {n = δ Π₂} {m = δ Π₁})
                  (≤-trans
                    (right-≤-max {n = max (δ Π₁) (δ Π₂)} {m = suc (degree A')})
                    (right-≤-max {n = max (suc (degree A')) (max (δ Π₁) (δ Π₂))} {m = δ Π₀}))))
              (mixGo
                {Γ₀ = Γ} {Δ₀ = Δ} {Γ₀' = Γ₂' ++ [ (A' ^ α') ]} {Δ₀' = Δ₂'}
                Π₀ Π₂ c₂
                (rec _ (step-lex-height (step-right-binary₂ (height Π₁) (height Π₂) (height Π₀)))))

          cutCase : Dec ((A' ^ α') ≡ (A ^ α))
            → MixResult nCut
                {Γ = Γ} {Δ = Δ}
                {Γ' = Γ₁' ++ Γ₂'} {Δ' = Δ₁' ++ Δ₂'}
                {A = A} {α = α}
          cutCase (yes eqAA) =
            mix-lift-right-Cut
              {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Γ₂' = Γ₂'} {Δ₁' = Δ₁'} {Δ₂' = Δ₂'}
              {A = A} {A' = A'} {α = α} {α' = α'}
              cCut' nCut dA'≤nCut r₁ (Π₂norm , dΠ₂norm≤nCut)
            where
              eqSingle : ([ (A' ^ α') ] -pf (A ^ α)) ≡ []
              eqSingle =
                pf-cons-eq
                  {φ = (A ^ α)} {ψ = (A' ^ α')} {Γ = []}
                  eqAA

              eqRem : ((Γ₂' ++ [ (A' ^ α') ]) -pf (A ^ α))
                   ≡ ((Γ₂' -pf (A ^ α)) ++ [])
              eqRem =
                pf-++ (A ^ α) Γ₂' [ (A' ^ α') ]
                ∙ cong ((Γ₂' -pf (A ^ α)) ++_) eqSingle

              eqCtx : (Γ ++ ((Γ₂' ++ [ (A' ^ α') ]) -pf (A ^ α)))
                   ≡ (Γ ++ ((Γ₂' -pf (A ^ α)) ++ []))
              eqCtx = cong (Γ ++_) eqRem

              Πmid₀ : (Γ ++ ((Γ₂' -pf (A ^ α)) ++ [])) ⊢ rhs₂
              Πmid₀ = subst (λ xs → xs ⊢ rhs₂) eqCtx (fst r₂raw)

              dΠmid₀≤nCut : δ Πmid₀ ≤ nCut
              dΠmid₀≤nCut =
                snd (subst-δ-Γ eqCtx (fst r₂raw) (snd r₂raw))

              subL₀ : (Γ ++ ((Γ₂' -pf (A ^ α)) ++ [])) ⊆ (Γ ++ (Γ₂' -pf (A ^ α)))
              subL₀ = solveCtx⊆!

              Πbase : (Γ ++ (Γ₂' -pf (A ^ α))) ⊢ rhs₂
              Πbase = structural subL₀ subset-refl Πmid₀

              dΠbase≤nCut : δ Πbase ≤ nCut
              dΠbase≤nCut =
                snd (structural-δ subL₀ subset-refl Πmid₀ dΠmid₀≤nCut)

              subL₁ : (Γ ++ (Γ₂' -pf (A ^ α)))
                  ⊆ ((Γ ++ (Γ₂' -pf (A ^ α))) ++ [ (A' ^ α') ])
              subL₁ = solveCtx⊆!

              Π₂norm : ((Γ ++ (Γ₂' -pf (A ^ α))) ++ [ (A' ^ α') ]) ⊢ rhs₂
              Π₂norm = structural subL₁ subset-refl Πbase

              dΠ₂norm≤nCut : δ Π₂norm ≤ nCut
              dΠ₂norm≤nCut =
                snd (structural-δ subL₁ subset-refl Πbase dΠbase≤nCut)

          cutCase (no a'≢a) =
            mix-lift-right-Cut
              {Γ = Γ} {Δ = Δ} {Γ₁' = Γ₁'} {Γ₂' = Γ₂'} {Δ₁' = Δ₁'} {Δ₂' = Δ₂'}
              {A = A} {A' = A'} {α = α} {α' = α'}
              cCut' nCut dA'≤nCut r₁ (Π₂norm , dΠ₂norm≤nCut)
            where
              eqSingle : ([ (A' ^ α') ] -pf (A ^ α)) ≡ [ (A' ^ α') ]
              eqSingle = pf-singleton-neq (λ q → a'≢a (sym q))

              eqRem : ((Γ₂' ++ [ (A' ^ α') ]) -pf (A ^ α))
                   ≡ ((Γ₂' -pf (A ^ α)) ++ [ (A' ^ α') ])
              eqRem =
                pf-++ (A ^ α) Γ₂' [ (A' ^ α') ]
                ∙ cong ((Γ₂' -pf (A ^ α)) ++_) eqSingle

              eqCtx : (Γ ++ ((Γ₂' ++ [ (A' ^ α') ]) -pf (A ^ α)))
                   ≡ (Γ ++ ((Γ₂' -pf (A ^ α)) ++ [ (A' ^ α') ]))
              eqCtx = cong (Γ ++_) eqRem

              Πmid₀ : (Γ ++ ((Γ₂' -pf (A ^ α)) ++ [ (A' ^ α') ])) ⊢ rhs₂
              Πmid₀ = subst (λ xs → xs ⊢ rhs₂) eqCtx (fst r₂raw)

              dΠmid₀≤nCut : δ Πmid₀ ≤ nCut
              dΠmid₀≤nCut =
                snd (subst-δ-Γ eqCtx (fst r₂raw) (snd r₂raw))

              subL : (Γ ++ ((Γ₂' -pf (A ^ α)) ++ [ (A' ^ α') ]))
                 ⊆ ((Γ ++ (Γ₂' -pf (A ^ α))) ++ [ (A' ^ α') ])
              subL = solveCtx⊆!

              Π₂norm : ((Γ ++ (Γ₂' -pf (A ^ α))) ++ [ (A' ^ α') ]) ⊢ rhs₂
              Π₂norm = structural subL subset-refl Πmid₀

              dΠ₂norm≤nCut : δ Π₂norm ≤ nCut
              dΠ₂norm≤nCut =
                snd (structural-δ subL subset-refl Πmid₀ dΠmid₀≤nCut)
      ... | _ | _ | _ = mixGo Π₀
        (Cut {A = A'} {α = α'} {Γ₁ = Γ₁'} {Γ₂ = Γ₂'} {Δ₁ = Δ₁'} {Δ₂ = Δ₂'} cCut Π₁ Π₂)
        c (acc rec)
      -- Modal right
      mixGoR {Γ₀ = Γ} {Δ₀ = Δ}
        Π₀ (BoxL {Γ = Γ'} {Δ = Δ'} {A = B} {α = β} {β = γ} mc Πsub) c (acc rec) =
        boxLCase ((□ B ^ β) ≟pf (A ^ α))
        where
          boxLCase : Dec ((□ B ^ β) ≡ (A ^ α))
            → MixResult (max (δ Π₀) (δ Πsub))
                {Γ = Γ} {Δ = Δ}
                {Γ' = Γ' ++ [ (□ B ^ β) ]} {Δ' = Δ'}
                {A = A} {α = α}
          boxLCase (yes _) = TODO
          boxLCase (no box≢a)
            with modalConstraint-rebuild
              {α = β} {β = γ}
              {Γ = Γ'} {Δ = Δ'}
              {Γ' = Γ ++ (Γ' -pf (A ^ α))}
              {Δ' = (Δ -pf (A ^ α)) ++ Δ'}
              mc
          ... | nothing = mixGo Π₀ (BoxL {Γ = Γ'} {Δ = Δ'} {A = B} {α = β} {β = γ} mc Πsub) c (acc rec)
          ... | just mc'
            with cutConstraint-down-right-BoxL
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {α = α} {β = β} {γ = γ}
              mc c
          ...   | just c↓ =
            mix-lift-right-BoxL
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {α = α} {β = β} {γ = γ}
              box≢a mc' (max (δ Π₀) (δ Πsub))
              (mixGo
                {Γ₀ = Γ} {Δ₀ = Δ}
                {Γ₀' = Γ' ++ [ (B ^ γ) ]} {Δ₀' = Δ'}
                Π₀ Πsub c↓
                (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))
          ...   | nothing = mixGo Π₀ (BoxL {Γ = Γ'} {Δ = Δ'} {A = B} {α = β} {β = γ} mc Πsub) c (acc rec)
      mixGoR Π₀ (BoxR fr Πsub) c wf = TODO
      mixGoR Π₀ (DiaL fr Πsub) c wf = TODO
      mixGoR {Γ₀ = Γ} {Δ₀ = Δ}
        Π₀ (DiaR {Γ = Γ'} {Δ = Δ'} {A = B} {α = β} {β = γ} mc Πsub) c (acc rec) =
        diaRCase ((♢ B ^ β) ≟pf (A ^ α))
        where
          diaRCase : Dec ((♢ B ^ β) ≡ (A ^ α))
            → MixResult (max (δ Π₀) (δ Πsub))
                {Γ = Γ} {Δ = Δ}
                {Γ' = Γ'} {Δ' = (♢ B ^ β) ∷ Δ'}
                {A = A} {α = α}
          diaRCase (yes _) = TODO
          diaRCase (no dia≢a)
            with modalConstraint-rebuild
              {α = β} {β = γ}
              {Γ = Γ'} {Δ = Δ'}
              {Γ' = Γ ++ (Γ' -pf (A ^ α))}
              {Δ' = (Δ -pf (A ^ α)) ++ Δ'}
              mc
          ... | nothing = mixGo Π₀ (DiaR {Γ = Γ'} {Δ = Δ'} {A = B} {α = β} {β = γ} mc Πsub) c (acc rec)
          ... | just mc' =
            mix-lift-right-DiaR
              {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
              {A = A} {B = B} {α = α} {β = β} {γ = γ}
              dia≢a mc' (max (δ Π₀) (δ Πsub))
              (mixGo
                {Γ₀ = Γ} {Δ₀ = Δ}
                {Γ₀' = Γ'} {Δ₀' = (B ^ γ) ∷ Δ'}
                Π₀ Πsub
                (cutConstraint-down-right-DiaR
                  {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'}
                  {A = A} {B = B} {α = α} {β = β} {γ = γ}
                  mc c)
                (rec _ (step-lex-height (step-right-+1 (height Π₀) (height Πsub)))))

mixWorker : ∀ {Γ Δ Γ' Δ'} {A : Formula} {α : Position}
  → (n : ℕ) → degree A ≡ n
  → (Π : Γ ⊢ Δ) → (Π' : Γ' ⊢ Δ')
  → δ Π ≤ n → δ Π' ≤ n
  → cutConstraint M A α Γ Γ' Δ Δ'
  → Acc _<Lex_ (n , mixHeight Π Π')
  → MixResult n {Γ} {Δ} {Γ'} {Δ'} {A} {α}
mixWorker {Γ} {Δ} {Γ'} {Δ'} {A} {α} n degEq Π Π' dΠ dΠ' c wf =
  liftMixResult
    {m = max (δ Π) (δ Π')} {n = n}
    {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {A = A} {α = α}
    (max-least dΠ dΠ')
    (mixWorkerRaw {Γ} {Δ} {Γ'} {Δ'} {A} {α} n degEq Π Π' c wf)

mix : MixAPI
mix {Γ} {Δ} {Γ'} {Δ'} {A} {α} n degEq Π Π' dΠ dΠ' c =
  mixWorker n degEq Π Π' dΠ dΠ' c (<Lex-wf (n , mixHeight Π Π'))
