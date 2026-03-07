{-# OPTIONS --safe #-}

-- Derivability examples for E_pos across modal logics
-- (OVERLAY25 paper, Section 5)

module NAMOR.Final.Test where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List
open import Cubical.Data.Nat hiding (_^_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)

open import NAMOR.List.Prefix
  using (_⊑_)
  renaming ([] to ⊑[]; _∷_ to _⊑∷_)
open import NAMOR.List.Any
  using (here; there)

open import NAMOR.Final.Syntax

private
  -- Non-empty position cannot be prefix of []
  ¬cons⊑[] : ∀ {a : ℕ} {as : List ℕ}
    → (a ∷ as) ⊑ [] → ⊥
  ¬cons⊑[] ()

  -- Freshness for singleton context with position []
  freshNil : ∀ {a : ℕ} {as : List ℕ} {B : Formula}
    → (a ∷ as) ∉Init [ B ^ [] ]
  freshNil (_ , here e , p) =
    ¬cons⊑[] (subst (_ ⊑_) (cong PFormula.pos e) p)

------------------------------------------------------------------------
-- S4: reflexivity + transitivity of □

module S4Test where
  open import NAMOR.Final.System S4

  -- Axiom T: □A → A
  axiomT : ∀ {A} → [] ⊢ [ (□ A ⇒ A) ^ [] ]
  axiomT = ImpR (BoxL {Γ = []} ⊑[] Ax)

  -- Axiom 4: □A → □□A
  axiom4 : ∀ {A} → [] ⊢ [ (□ A ⇒ □ (□ A)) ^ [] ]
  axiom4 = ImpR
    (BoxR {x = 0} freshNil
      (BoxR {x = 1} freshNil
        (BoxL {Γ = []} ⊑[] Ax)))

------------------------------------------------------------------------
-- T: reflexivity of □ (successor constraint)

module TTest where
  open import NAMOR.Final.System T

  -- Axiom T: □A → A (modalConstraint T [] [] = [] ◃⁰ [])
  axiomT : ∀ {A} → [] ⊢ [ (□ A ⇒ A) ^ [] ]
  axiomT = ImpR (BoxL {Γ = []} (inl refl) Ax)

------------------------------------------------------------------------
-- S5: universal access (trivial constraint)

module S5Test where
  open import NAMOR.Final.System S5

  -- Axiom T: □A → A
  axiomT : ∀ {A} → [] ⊢ [ (□ A ⇒ A) ^ [] ]
  axiomT = ImpR (BoxL {Γ = []} tt Ax)

  -- Axiom B: A → □♢A
  axiomB : ∀ {A} → [] ⊢ [ (A ⇒ □ (♢ A)) ^ [] ]
  axiomB = ImpR
    (BoxR {x = 0} freshNil (DiaR tt Ax))

  -- Axiom 4: □A → □□A
  axiom4 : ∀ {A} → [] ⊢ [ (□ A ⇒ □ (□ A)) ^ [] ]
  axiom4 = ImpR
    (BoxR {x = 0} freshNil
      (BoxR {x = 1} freshNil
        (BoxL {Γ = []} tt Ax)))

  -- Axiom 5: ♢A → □♢A
  axiom5 : ∀ {A} → [] ⊢ [ (♢ A ⇒ □ (♢ A)) ^ [] ]
  axiom5 {A} = ImpR
    (DiaL {[]} {_} {_} {[]} {0} freshNil
      (BoxR {x = 1} fresh1 (DiaR tt Ax)))
    where
    fresh1 : [ 1 ] ∉Init [ A ^ [ 0 ] ]
    fresh1 (_ , here e , p) with
      subst (_ ⊑_) (cong PFormula.pos e) p
    ... | eq ⊑∷ _ = snotz eq

------------------------------------------------------------------------
-- Geach (.2): failure in S4, success in S4.2

module GeachTest where
  open import NAMOR.Final.System S4dot2
  open import NAMOR.Final.Equivalence.HilbertCompleteness S4dot2
    using (derive-C)

  -- %<*axiomGFailed>
  axiomGFailed : modalConstraint S4 [ 1 ] ([ 0 ] ++ [ 1 ]) [] [] → ⊥
  axiomGFailed (eq ⊑∷ _) = snotz eq
  -- %</axiomGFailed>

  -- %<*axiomGCorrect>
  axiomGCorrect : ∀ {A : Formula} → [] ⊢ [ (♢ (□ A) ⇒ □ (♢ A)) ^ [] ]
  axiomGCorrect = derive-C tt
  -- %</axiomGCorrect>
