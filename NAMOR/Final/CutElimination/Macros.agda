{-# OPTIONS --safe #-}

module NAMOR.Final.CutElimination.Macros where

open import Cubical.Data.Unit using (Unit)
open import Agda.Builtin.Reflection hiding (Type)

open import NAMOR.Final.Syntax using (_-pf_; _≟pfʳ_)
open import NAMOR.Solver.Subset.Reflection using (solve⊆-tc)

private
  solveCtx⊆!-macro : Term → TC Unit
  solveCtx⊆!-macro hole = solve⊆-tc (quoteTerm _-pf_) (quoteTerm _≟pfʳ_) hole

macro
  solveCtx⊆! : Term → TC _
  solveCtx⊆! = solveCtx⊆!-macro
