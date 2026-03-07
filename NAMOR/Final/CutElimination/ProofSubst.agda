{-# OPTIONS --safe #-}

open import NAMOR.Final.Syntax using (Logic)

module NAMOR.Final.CutElimination.ProofSubst (M : Logic) where

open import Cubical.Foundations.Prelude
  using (Type; _≡_; refl; cong; sym; subst; _∙_; cong₂; subst2)
open import Cubical.Data.List using (List; _∷_; []; _++_; [_])
open import Cubical.Data.List.Properties using (++-assoc)
open import Cubical.Data.Sigma using (_×_; _,_; Σ)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary renaming (¬_ to Neg)

open import NAMOR.Final.Syntax hiding (Logic; Not)
open import NAMOR.Final.System M
open import NAMOR.Final.CutElimination.Defs M

------------------------------------------------------------------------
-- Side conditions for substitution over proofs.
--
-- This mirrors the S4dot2 strategy: substitution is defined recursively,
-- and modal/cut side-conditions are carried explicitly so rule
-- reconstruction is constructive and --safe.

SubstSideCond : (ρ τ : Position) → ∀ {Γ Δ} → (Γ ⊢ Δ) → Type
SubstSideCond ρ τ Ax = Unit
SubstSideCond ρ τ
  (Cut {A} {α} {Γ₁} {Γ₂} {Δ₁} {Δ₂} _ Π₁ Π₂) =
    cutConstraint M A (substPos ρ τ α)
      (substContext ρ τ Γ₁) (substContext ρ τ Γ₂)
      (substContext ρ τ Δ₁) (substContext ρ τ Δ₂)
    × SubstSideCond ρ τ Π₁
    × SubstSideCond ρ τ Π₂
SubstSideCond ρ τ (WeakenL Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (WeakenR Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (ContractL Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (ContractR Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (ExchangeL Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (ExchangeR Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (NotL Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (NotR Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (AndL1 Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (AndL2 Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (AndR Π₁ Π₂) =
  SubstSideCond ρ τ Π₁ × SubstSideCond ρ τ Π₂
SubstSideCond ρ τ (OrL Π₁ Π₂) =
  SubstSideCond ρ τ Π₁ × SubstSideCond ρ τ Π₂
SubstSideCond ρ τ (OrR1 Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (OrR2 Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (ImpL Π₁ Π₂) =
  SubstSideCond ρ τ Π₁ × SubstSideCond ρ τ Π₂
SubstSideCond ρ τ (ImpR Π) = SubstSideCond ρ τ Π
SubstSideCond ρ τ (BoxL {Γ} {Δ} {A} {α} {β} _ Π) =
  modalConstraint M (substPos ρ τ α) (substPos ρ τ β)
    (substContext ρ τ Γ) (substContext ρ τ Δ)
  × SubstSideCond ρ τ Π
SubstSideCond ρ τ (BoxR {Γ} {Δ} {A} {α} {x} _ Π) =
  (substPos ρ τ (α ∘ [ x ]) ≡ (substPos ρ τ α ∘ [ x ]))
  × (((substPos ρ τ α ∘ [ x ]) ∉Init
      (substContext ρ τ Γ ++ substContext ρ τ Δ))
  × SubstSideCond ρ τ Π)
SubstSideCond ρ τ (DiaL {Γ} {Δ} {A} {α} {x} _ Π) =
  (substPos ρ τ (α ∘ [ x ]) ≡ (substPos ρ τ α ∘ [ x ]))
  × (((substPos ρ τ α ∘ [ x ]) ∉Init
      (substContext ρ τ Γ ++ substContext ρ τ Δ))
  × SubstSideCond ρ τ Π)
SubstSideCond ρ τ (DiaR {Γ} {Δ} {A} {α} {β} _ Π) =
  modalConstraint M (substPos ρ τ α) (substPos ρ τ β)
    (substContext ρ τ Γ) (substContext ρ τ Δ)
  × SubstSideCond ρ τ Π

------------------------------------------------------------------------
-- Raw substitution on derivations (under explicit side conditions)

substProofRaw :
  ∀ {Γ Δ} (ρ τ : Position)
  → (Π : Γ ⊢ Δ)
  → SubstSideCond ρ τ Π
  → substContext ρ τ Γ ⊢ substContext ρ τ Δ
substProofRaw ρ τ Ax _ = Ax

substProofRaw ρ τ
  (Cut {A} {α} {Γ₁} {Γ₂} {Δ₁} {Δ₂} _ Π₁ Π₂)
  (c' , sc₁ , sc₂) =
  subst2 _⊢_
    (sym (substContext-++ ρ τ Γ₁ Γ₂))
    (sym (substContext-++ ρ τ Δ₁ Δ₂))
    (Cut c'
      (subst (substContext ρ τ Γ₁ ⊢_)
        (substContext-++ ρ τ [ (A ^ α) ] Δ₁)
        (substProofRaw ρ τ Π₁ sc₁))
      (subst (_⊢ substContext ρ τ Δ₂)
        (substContext-++ ρ τ Γ₂ [ (A ^ α) ])
        (substProofRaw ρ τ Π₂ sc₂)))

substProofRaw ρ τ (WeakenL Π) sc = WeakenL (substProofRaw ρ τ Π sc)
substProofRaw ρ τ (WeakenR Π) sc = WeakenR (substProofRaw ρ τ Π sc)
substProofRaw ρ τ (ContractL Π) sc = ContractL (substProofRaw ρ τ Π sc)
substProofRaw ρ τ (ContractR Π) sc = ContractR (substProofRaw ρ τ Π sc)

substProofRaw ρ τ
  (ExchangeL {Γ₁} {Γ₂} {Δ} {c} {d} Π) sc =
  let
    Π' = substProofRaw ρ τ Π sc

    lhs-path :
      substContext ρ τ (Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂)
      ≡ substContext ρ τ Γ₁
        ++ [ substPFormula ρ τ c ]
        ++ [ substPFormula ρ τ d ]
        ++ substContext ρ τ Γ₂
    lhs-path =
      substContext-++ ρ τ Γ₁ ([ c ] ++ [ d ] ++ Γ₂)
      ∙ cong (substContext ρ τ Γ₁ ++_)
          (substContext-++ ρ τ [ c ] ([ d ] ++ Γ₂)
          ∙ cong (substContext ρ τ [ c ] ++_)
              (substContext-++ ρ τ [ d ] Γ₂))

    rhs-path :
      substContext ρ τ (Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂)
      ≡ substContext ρ τ Γ₁
        ++ [ substPFormula ρ τ d ]
        ++ [ substPFormula ρ τ c ]
        ++ substContext ρ τ Γ₂
    rhs-path =
      substContext-++ ρ τ Γ₁ ([ d ] ++ [ c ] ++ Γ₂)
      ∙ cong (substContext ρ τ Γ₁ ++_)
          (substContext-++ ρ τ [ d ] ([ c ] ++ Γ₂)
          ∙ cong (substContext ρ τ [ d ] ++_)
              (substContext-++ ρ τ [ c ] Γ₂))

    Π'' :
      (substContext ρ τ Γ₁
        ++ [ substPFormula ρ τ c ]
        ++ [ substPFormula ρ τ d ]
        ++ substContext ρ τ Γ₂) ⊢ substContext ρ τ Δ
    Π'' = subst (_⊢ substContext ρ τ Δ) lhs-path Π'

    raw :
      (substContext ρ τ Γ₁
        ++ [ substPFormula ρ τ d ]
        ++ [ substPFormula ρ τ c ]
        ++ substContext ρ τ Γ₂) ⊢ substContext ρ τ Δ
    raw = ExchangeL Π''
  in subst (_⊢ substContext ρ τ Δ) (sym rhs-path) raw

substProofRaw ρ τ
  (ExchangeR {Γ} {Δ₁} {Δ₂} {c} {d} Π) sc =
  let
    Π' = substProofRaw ρ τ Π sc

    lhs-path :
      substContext ρ τ (Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂)
      ≡ substContext ρ τ Δ₁
        ++ [ substPFormula ρ τ c ]
        ++ [ substPFormula ρ τ d ]
        ++ substContext ρ τ Δ₂
    lhs-path =
      substContext-++ ρ τ Δ₁ ([ c ] ++ [ d ] ++ Δ₂)
      ∙ cong (substContext ρ τ Δ₁ ++_)
          (substContext-++ ρ τ [ c ] ([ d ] ++ Δ₂)
          ∙ cong (substContext ρ τ [ c ] ++_)
              (substContext-++ ρ τ [ d ] Δ₂))

    rhs-path :
      substContext ρ τ (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂)
      ≡ substContext ρ τ Δ₁
        ++ [ substPFormula ρ τ d ]
        ++ [ substPFormula ρ τ c ]
        ++ substContext ρ τ Δ₂
    rhs-path =
      substContext-++ ρ τ Δ₁ ([ d ] ++ [ c ] ++ Δ₂)
      ∙ cong (substContext ρ τ Δ₁ ++_)
          (substContext-++ ρ τ [ d ] ([ c ] ++ Δ₂)
          ∙ cong (substContext ρ τ [ d ] ++_)
              (substContext-++ ρ τ [ c ] Δ₂))

    Π'' :
      substContext ρ τ Γ ⊢
      (substContext ρ τ Δ₁
        ++ [ substPFormula ρ τ c ]
        ++ [ substPFormula ρ τ d ]
        ++ substContext ρ τ Δ₂)
    Π'' = subst (substContext ρ τ Γ ⊢_) lhs-path Π'

    raw :
      substContext ρ τ Γ ⊢
      (substContext ρ τ Δ₁
        ++ [ substPFormula ρ τ d ]
        ++ [ substPFormula ρ τ c ]
        ++ substContext ρ τ Δ₂)
    raw = ExchangeR Π''
  in subst (substContext ρ τ Γ ⊢_) (sym rhs-path) raw

substProofRaw ρ τ (NotL Π) sc = NotL (substProofRaw ρ τ Π sc)
substProofRaw ρ τ (NotR Π) sc = NotR (substProofRaw ρ τ Π sc)
substProofRaw ρ τ (AndL1 Π) sc = AndL1 (substProofRaw ρ τ Π sc)
substProofRaw ρ τ (AndL2 Π) sc = AndL2 (substProofRaw ρ τ Π sc)

substProofRaw ρ τ (AndR {Γ₁} {a} {α} {Δ₁} {Γ₂} {b} {Δ₂} Π₁ Π₂)
  (sc₁ , sc₂) =
  let
    p1 = substProofRaw ρ τ Π₁ sc₁
    p2 = substProofRaw ρ τ Π₂ sc₂
    raw = AndR p1 p2

    lhs-path : substContext ρ τ (Γ₁ ++ Γ₂)
      ≡ substContext ρ τ Γ₁ ++ substContext ρ τ Γ₂
    lhs-path = substContext-++ ρ τ Γ₁ Γ₂

    rhs-path : substContext ρ τ ((And a b ^ α) ∷ (Δ₁ ++ Δ₂))
      ≡ (substPFormula ρ τ (And a b ^ α) ∷
         (substContext ρ τ Δ₁ ++ substContext ρ τ Δ₂))
    rhs-path = cong (substPFormula ρ τ (And a b ^ α) ∷_)
      (substContext-++ ρ τ Δ₁ Δ₂)
  in subst2 _⊢_ (sym lhs-path) (sym rhs-path) raw

substProofRaw ρ τ (OrL {a} {α} {Γ₁} {Δ₁} {b} {Γ₂} {Δ₂} Π₁ Π₂)
  (sc₁ , sc₂) =
  let
    p1 = substProofRaw ρ τ Π₁ sc₁
    p2 = substProofRaw ρ τ Π₂ sc₂
    raw = OrL p1 p2

    lhs-path : substContext ρ τ ((Or a b ^ α) ∷ (Γ₁ ++ Γ₂))
      ≡ (substPFormula ρ τ (Or a b ^ α) ∷
         (substContext ρ τ Γ₁ ++ substContext ρ τ Γ₂))
    lhs-path = cong (substPFormula ρ τ (Or a b ^ α) ∷_)
      (substContext-++ ρ τ Γ₁ Γ₂)

    rhs-path : substContext ρ τ (Δ₁ ++ Δ₂)
      ≡ substContext ρ τ Δ₁ ++ substContext ρ τ Δ₂
    rhs-path = substContext-++ ρ τ Δ₁ Δ₂
  in subst2 _⊢_ (sym lhs-path) (sym rhs-path) raw

substProofRaw ρ τ (OrR1 Π) sc = OrR1 (substProofRaw ρ τ Π sc)
substProofRaw ρ τ (OrR2 Π) sc = OrR2 (substProofRaw ρ τ Π sc)

substProofRaw ρ τ (ImpL {Γ₁} {a} {α} {Δ₁} {b} {Γ₂} {Δ₂} Π₁ Π₂)
  (sc₁ , sc₂) =
  let
    p1 = substProofRaw ρ τ Π₁ sc₁
    p2 = substProofRaw ρ τ Π₂ sc₂
    raw = ImpL p1 p2

    lhs-path : substContext ρ τ ((a ⇒ b ^ α) ∷ (Γ₁ ++ Γ₂))
      ≡ (substPFormula ρ τ (a ⇒ b ^ α) ∷
         (substContext ρ τ Γ₁ ++ substContext ρ τ Γ₂))
    lhs-path = cong (substPFormula ρ τ (a ⇒ b ^ α) ∷_)
      (substContext-++ ρ τ Γ₁ Γ₂)

    rhs-path : substContext ρ τ (Δ₁ ++ Δ₂)
      ≡ substContext ρ τ Δ₁ ++ substContext ρ τ Δ₂
    rhs-path = substContext-++ ρ τ Δ₁ Δ₂
  in subst2 _⊢_ (sym lhs-path) (sym rhs-path) raw

substProofRaw ρ τ (ImpR Π) sc = ImpR (substProofRaw ρ τ Π sc)

substProofRaw ρ τ
  (BoxL {Γ} {Δ} {a} {α} {β} _ Π)
  (c' , sc) =
  let
    p = substProofRaw ρ τ Π sc

    lhs-path :
      substContext ρ τ (Γ ++ [ (a ^ β) ])
      ≡ substContext ρ τ Γ ++ [ (a ^ substPos ρ τ β) ]
    lhs-path = substContext-++ ρ τ Γ [ (a ^ β) ]

    p' : (substContext ρ τ Γ ++ [ (a ^ substPos ρ τ β) ])
         ⊢ substContext ρ τ Δ
    p' = subst (_⊢ substContext ρ τ Δ) lhs-path p

    raw : (substContext ρ τ Γ ++ [ (□ a ^ substPos ρ τ α) ])
          ⊢ substContext ρ τ Δ
    raw = BoxL c' p'

    out-path :
      substContext ρ τ (Γ ++ [ (□ a ^ α) ])
      ≡ substContext ρ τ Γ ++ [ (□ a ^ substPos ρ τ α) ]
    out-path = substContext-++ ρ τ Γ [ (□ a ^ α) ]
  in subst (_⊢ substContext ρ τ Δ) (sym out-path) raw

substProofRaw ρ τ
  (BoxR {Γ} {Δ} {a} {α} {x} _ Π)
  (eq-pos , fr' , sc) =
  let
    p = substProofRaw ρ τ Π sc

    rhs-path :
      substContext ρ τ ([ (a ^ (α ∘ [ x ])) ] ++ Δ)
      ≡ [ (a ^ (substPos ρ τ α ∘ [ x ])) ] ++ substContext ρ τ Δ
    rhs-path =
      substContext-++ ρ τ [ (a ^ (α ∘ [ x ])) ] Δ
      ∙ cong (λ q → [ (a ^ q) ] ++ substContext ρ τ Δ) eq-pos

    p' : substContext ρ τ Γ
         ⊢ ([ (a ^ (substPos ρ τ α ∘ [ x ])) ] ++ substContext ρ τ Δ)
    p' = subst (substContext ρ τ Γ ⊢_) rhs-path p

    raw : substContext ρ τ Γ
          ⊢ ([ (□ a ^ substPos ρ τ α) ] ++ substContext ρ τ Δ)
    raw = BoxR fr' p'

    out-path :
      substContext ρ τ ([ (□ a ^ α) ] ++ Δ)
      ≡ [ (□ a ^ substPos ρ τ α) ] ++ substContext ρ τ Δ
    out-path = substContext-++ ρ τ [ (□ a ^ α) ] Δ
  in subst (substContext ρ τ Γ ⊢_) (sym out-path) raw

substProofRaw ρ τ
  (DiaL {Γ} {Δ} {a} {α} {x} _ Π)
  (eq-pos , fr' , sc) =
  let
    p = substProofRaw ρ τ Π sc

    lhs-path :
      substContext ρ τ (Γ ++ [ (a ^ (α ∘ [ x ])) ])
      ≡ substContext ρ τ Γ ++ [ (a ^ (substPos ρ τ α ∘ [ x ])) ]
    lhs-path =
      substContext-++ ρ τ Γ [ (a ^ (α ∘ [ x ])) ]
      ∙ cong (substContext ρ τ Γ ++_)
          (cong [_] (cong (a ^_) eq-pos))

    p' : (substContext ρ τ Γ ++ [ (a ^ (substPos ρ τ α ∘ [ x ])) ])
         ⊢ substContext ρ τ Δ
    p' = subst (_⊢ substContext ρ τ Δ) lhs-path p

    raw : (substContext ρ τ Γ ++ [ (♢ a ^ substPos ρ τ α) ])
          ⊢ substContext ρ τ Δ
    raw = DiaL fr' p'

    out-path :
      substContext ρ τ (Γ ++ [ (♢ a ^ α) ])
      ≡ substContext ρ τ Γ ++ [ (♢ a ^ substPos ρ τ α) ]
    out-path = substContext-++ ρ τ Γ [ (♢ a ^ α) ]
  in subst (_⊢ substContext ρ τ Δ) (sym out-path) raw

substProofRaw ρ τ
  (DiaR {Γ} {Δ} {a} {α} {β} _ Π)
  (c' , sc) =
  let
    p = substProofRaw ρ τ Π sc

    rhs-path :
      substContext ρ τ ([ (a ^ β) ] ++ Δ)
      ≡ [ (a ^ substPos ρ τ β) ] ++ substContext ρ τ Δ
    rhs-path = substContext-++ ρ τ [ (a ^ β) ] Δ

    p' : substContext ρ τ Γ
         ⊢ [ (a ^ substPos ρ τ β) ] ++ substContext ρ τ Δ
    p' = subst (substContext ρ τ Γ ⊢_) rhs-path p

    raw : substContext ρ τ Γ
          ⊢ [ (♢ a ^ substPos ρ τ α) ] ++ substContext ρ τ Δ
    raw = DiaR c' p'

    out-path :
      substContext ρ τ ([ (♢ a ^ α) ] ++ Δ)
      ≡ [ (♢ a ^ substPos ρ τ α) ] ++ substContext ρ τ Δ
    out-path = substContext-++ ρ τ [ (♢ a ^ α) ] Δ
  in subst (substContext ρ τ Γ ⊢_) (sym out-path) raw

------------------------------------------------------------------------
-- Global normalization wrapper (identity for current representation).

makeWellFormed : ∀ {Γ Δ} → Γ ⊢ Δ → Γ ⊢ Δ
makeWellFormed Π = Π

makeWellFormed-height : ∀ {Γ Δ} (Π : Γ ⊢ Δ)
  → height (makeWellFormed Π) ≡ height Π
makeWellFormed-height Π = refl

makeWellFormed-δ : ∀ {Γ Δ} (Π : Γ ⊢ Δ)
  → δ (makeWellFormed Π) ≡ δ Π
makeWellFormed-δ Π = refl

------------------------------------------------------------------------
-- High-level exported alias (next step: wrapper deriving side conditions)

substProof :
  ∀ {Γ Δ} (ρ τ : Position)
  → (Π : Γ ⊢ Δ)
  → SubstSideCond ρ τ Π
  → substContext ρ τ Γ ⊢ substContext ρ τ Δ
substProof = substProofRaw
