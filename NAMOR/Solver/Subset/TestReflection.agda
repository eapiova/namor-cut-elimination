{-# OPTIONS --safe #-}

module NAMOR.Solver.Subset.TestReflection where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List; []; _∷_; [_]; _++_)

open import NAMOR.List.Membership using (_⊆_)
open import NAMOR.Final.Syntax
  using (PFormula; Ctx; _-pf_; _≟pfʳ_)
open import NAMOR.Solver.Subset.Reflection using (solve⊆!)
open import NAMOR.Final.CutElimination.Macros using (solveCtx⊆!)

test-append : ∀ (x : PFormula) (Γ : Ctx) → [ x ] ⊆ (Γ ++ [ x ])
test-append x Γ = solveCtx⊆!

test-remove : ∀ (x y : PFormula) (Γ : Ctx) → [ y ] ⊆ ([ y ] ++ (Γ -pf x))
test-remove x y Γ = solveCtx⊆!

test-duplicate : ∀ (x y : PFormula) (Γ : Ctx)
  → ((x ∷ Γ) -pf y) ⊆ ((x ∷ x ∷ Γ) -pf y)
test-duplicate x y Γ = solveCtx⊆!

test-swap : ∀ (x c d : PFormula) (Γ : Ctx)
  → ((Γ ++ [ c ] ++ [ d ]) -pf x) ⊆ ((Γ ++ [ d ] ++ [ c ]) -pf x)
test-swap x c d Γ = solveCtx⊆!

test-generic : ∀ (x y : PFormula) (Γ : Ctx)
  → [ y ] ⊆ ([ y ] ++ (Γ -pf x))
test-generic x y Γ = solve⊆! _-pf_ _≟pfʳ_

test-generic-quoted : ∀ (x y : PFormula) (Γ : Ctx)
  → [ y ] ⊆ ([ y ] ++ (Γ -pf x))
test-generic-quoted x y Γ = solve⊆! (quote _-pf_) _≟pfʳ_

test-contract-pf-right : ∀ (Aα Cγ : PFormula) (Γ' Δ' : Ctx)
  → ((((Cγ ∷ Γ') -pf Aα) ++ Δ') ⊆ ((((Cγ ∷ Cγ ∷ Γ') -pf Aα) ++ Δ')))
test-contract-pf-right Aα Cγ Γ' Δ' = solveCtx⊆!

test-contract-pf-left : ∀ (Aα Cγ : PFormula) (Γ Δ : Ctx)
  → ((Γ ++ ((Cγ ∷ Δ) -pf Aα)) ⊆ (Γ ++ ((Cγ ∷ Cγ ∷ Δ) -pf Aα)))
test-contract-pf-left Aα Cγ Γ Δ = solveCtx⊆!

test-weaken-pf-right : ∀ (Aα Cγ : PFormula) (Γ Δ : Ctx)
  → ((Γ ++ (Δ -pf Aα)) ⊆ (Γ ++ ((Cγ ∷ Δ) -pf Aα)))
test-weaken-pf-right Aα Cγ Γ Δ = solveCtx⊆!
