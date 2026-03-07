{-# OPTIONS #-}

open import NAMOR.Final.Syntax using (Logic)

module NAMOR.Final.CutElimination.Consistency (M : Logic) where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; subst)
open import Cubical.Data.Nat using (ℕ; zero; suc; max)
open import Cubical.Data.Nat.Order using (_≤_; ≤0→≡0; left-≤-max)
open import Cubical.Data.Nat.Properties using (snotz)
open import Cubical.Data.Sigma using (fst; snd)
open import Cubical.Data.List using (List; []; _∷_; _++_; [_])
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit; tt)

open import NAMOR.Final.Syntax hiding (Logic; Not)
open import NAMOR.Final.System M
open import NAMOR.Final.CutElimination.Defs M using (degree; δ; isCutFree)
open import NAMOR.Final.CutElimination.CutElimination M using (CutEliminationWith)
open import NAMOR.Final.CutElimination.Mix M using (MixAPI)

private
  ∷≠[] : {A : Type} {x : A} {xs : List A} → x ∷ xs ≡ [] → ⊥
  ∷≠[] eq = subst (λ { [] → ⊥ ; (_ ∷ _) → Unit }) eq tt

  ++-conicalˡ : {A : Type} (xs ys : List A) → xs ++ ys ≡ [] → xs ≡ []
  ++-conicalˡ [] ys eq = refl
  ++-conicalˡ (x ∷ xs) ys eq = ⊥-rec (∷≠[] eq)

  ++-conicalʳ : {A : Type} (xs ys : List A) → xs ++ ys ≡ [] → ys ≡ []
  ++-conicalʳ [] ys eq = eq
  ++-conicalʳ (x ∷ xs) ys eq = ⊥-rec (∷≠[] eq)

  suc-not-≤-zero : {n : ℕ} → suc n ≤ zero → ⊥
  suc-not-≤-zero sn≤0 = snotz (≤0→≡0 sn≤0)

  suc-≤-max : (n m : ℕ) → suc n ≤ max (suc n) m
  suc-≤-max n m = left-≤-max {m = suc n} {n = m}

  max-suc-neq-zero : {n m : ℕ} → max (suc n) m ≡ zero → ⊥
  max-suc-neq-zero {n} {m} eq =
    suc-not-≤-zero (subst (suc n ≤_) eq (suc-≤-max n m))

  exchange-ctx-neq[] : {Γ₁ Γ₂ : Ctx} {c d : PFormula}
    → Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂ ≡ [] → ⊥
  exchange-ctx-neq[] {Γ₁} {Γ₂} {c} {d} eq =
    ∷≠[] (++-conicalˡ [ d ] ([ c ] ++ Γ₂)
      (++-conicalʳ Γ₁ ([ d ] ++ [ c ] ++ Γ₂) eq))

noCutFreeProofOfEmpty : (Π : [] ⊢ []) → isCutFree Π → ⊥
noCutFreeProofOfEmpty Π cf = helper Π refl refl cf
  where
    helper : {Γ Δ : Ctx} → (Π : Γ ⊢ Δ)
      → Γ ≡ [] → Δ ≡ [] → δ Π ≡ zero → ⊥
    helper (Cut {A = A} c Π₁ Π₂) Γ≡[] Δ≡[] δ≡0 =
      max-suc-neq-zero {n = degree A} {m = max (δ Π₁) (δ Π₂)} δ≡0
    helper Ax Γ≡[] Δ≡[] δ≡0 = ∷≠[] Γ≡[]
    helper (WeakenL Π) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Γ≡[]
    helper (WeakenR Π) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    helper (ContractL Π) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Γ≡[]
    helper (ContractR Π) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    helper (ExchangeL {C = c} {D = d} Π) Γ≡[] Δ≡[] δ≡0 =
      exchange-ctx-neq[] Γ≡[]
    helper (ExchangeR {C = c} {D = d} Π) Γ≡[] Δ≡[] δ≡0 =
      exchange-ctx-neq[] Δ≡[]
    helper (NotL Π) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Γ≡[]
    helper (NotR Π) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    helper (AndL1 Π) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Γ≡[]
    helper (AndL2 Π) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Γ≡[]
    helper (AndR Π₁ Π₂) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    helper (OrL Π₁ Π₂) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Γ≡[]
    helper (OrR1 Π) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    helper (OrR2 Π) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    helper (ImpL Π₁ Π₂) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Γ≡[]
    helper (ImpR Π) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    helper (BoxL {Γ = Γ} {A = A} {α = α} c Π) Γ≡[] Δ≡[] δ≡0 =
      ∷≠[] (++-conicalʳ Γ [ (□ A ^ α) ] Γ≡[])
    helper (BoxR {Δ = Δ} {A = A} {α = α} fr Π) Γ≡[] Δ≡[] δ≡0 =
      ∷≠[] (++-conicalˡ [ (□ A ^ α) ] Δ Δ≡[])
    helper (DiaL {Γ = Γ} {A = A} {α = α} fr Π) Γ≡[] Δ≡[] δ≡0 =
      ∷≠[] (++-conicalʳ Γ [ (♢ A ^ α) ] Γ≡[])
    helper (DiaR {Δ = Δ} {A = A} {α = α} c Π) Γ≡[] Δ≡[] δ≡0 =
      ∷≠[] (++-conicalˡ [ (♢ A ^ α) ] Δ Δ≡[])

-- %<*consistency>
Consistency : MixAPI → ([] ⊢ []) → ⊥
Consistency mix Π =
  let
    Π* = fst (CutEliminationWith mix Π)
    cf* = snd (CutEliminationWith mix Π)
  in noCutFreeProofOfEmpty Π* cf*
-- %</consistency>
