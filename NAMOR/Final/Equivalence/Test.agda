{-# OPTIONS --safe #-}

module NAMOR.Final.Equivalence.Test where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List using ([]; [_])
open import Cubical.Data.Unit using (tt)

open import NAMOR.Final.Syntax
open import NAMOR.Final.Hilbert

module KSmoke where
  open import NAMOR.Final.Equivalence.HilbertCompleteness K
  open import NAMOR.Final.System K

  k-hilbert : ∀ {A B : Formula} → K ⊢ₕ (□ (A ⇒ B) ⇒ (□ A ⇒ □ B))
  k-hilbert = ax AxK

  k-sequent : ∀ {A B : Formula} → [] ⊢ [ (□ (A ⇒ B) ⇒ (□ A ⇒ □ B)) ^ [] ]
  k-sequent = completeness k-hilbert

module DSmoke where
  open import NAMOR.Final.Equivalence.HilbertCompleteness D
  open import NAMOR.Final.System D

  d-hilbert : ∀ {A : Formula} → D ⊢ₕ (□ A ⇒ ♢ A)
  d-hilbert = ax (AxD tt)

  d-sequent : ∀ {A : Formula} → [] ⊢ [ (□ A ⇒ ♢ A) ^ [] ]
  d-sequent = completeness d-hilbert

module TSmoke where
  open import NAMOR.Final.Equivalence.HilbertCompleteness T
  open import NAMOR.Final.System T

  t-hilbert : ∀ {A : Formula} → T ⊢ₕ (□ A ⇒ A)
  t-hilbert = ax (AxT tt)

  t-sequent : ∀ {A : Formula} → [] ⊢ [ (□ A ⇒ A) ^ [] ]
  t-sequent = completeness t-hilbert

module K4Smoke where
  open import NAMOR.Final.Equivalence.HilbertCompleteness K4
  open import NAMOR.Final.System K4

  k4-hilbert : ∀ {A : Formula} → K4 ⊢ₕ (□ A ⇒ □ (□ A))
  k4-hilbert = ax (Ax4 tt)

  k4-sequent : ∀ {A : Formula} → [] ⊢ [ (□ A ⇒ □ (□ A)) ^ [] ]
  k4-sequent = completeness k4-hilbert

module D4Smoke where
  open import NAMOR.Final.Equivalence.HilbertCompleteness D4
  open import NAMOR.Final.System D4

  d4-hilbert : ∀ {A : Formula} → D4 ⊢ₕ (□ A ⇒ □ (□ A))
  d4-hilbert = ax (Ax4 tt)

  d4-sequent : ∀ {A : Formula} → [] ⊢ [ (□ A ⇒ □ (□ A)) ^ [] ]
  d4-sequent = completeness d4-hilbert

module S4Smoke where
  open import NAMOR.Final.Equivalence.HilbertCompleteness S4
  open import NAMOR.Final.System S4

  s4-hilbert : ∀ {A : Formula} → S4 ⊢ₕ (□ A ⇒ A)
  s4-hilbert = ax (AxT tt)

  s4-sequent : ∀ {A : Formula} → [] ⊢ [ (□ A ⇒ A) ^ [] ]
  s4-sequent = completeness s4-hilbert

module S4dot2Smoke where
  open import NAMOR.Final.Equivalence.HilbertCompleteness S4dot2
  open import NAMOR.Final.System S4dot2

  s42-hilbert : ∀ {A : Formula} → S4dot2 ⊢ₕ (♢ (□ A) ⇒ □ (♢ A))
  s42-hilbert = ax (AxC tt)

  s42-sequent : ∀ {A : Formula} → [] ⊢ [ (♢ (□ A) ⇒ □ (♢ A)) ^ [] ]
  s42-sequent = completeness s42-hilbert

module S5Smoke where
  open import NAMOR.Final.Equivalence.HilbertCompleteness S5
  open import NAMOR.Final.System S5

  s5-hilbert : ∀ {A : Formula} → S5 ⊢ₕ (♢ A ⇒ □ (♢ A))
  s5-hilbert = ax (Ax5 tt)

  s5-sequent : ∀ {A : Formula} → [] ⊢ [ (♢ A ⇒ □ (♢ A)) ^ [] ]
  s5-sequent = completeness s5-hilbert

module S4Composed where
  open import NAMOR.Final.Equivalence.HilbertCompleteness S4
  open import NAMOR.Final.System S4

  id-hilbert : ∀ {A : Formula} → S4 ⊢ₕ (A ⇒ A)
  id-hilbert {A} =
    MP
      (ax (P1 {A = A} {B = A}))
      (MP
        (ax (P1 {A = A} {B = A ⇒ A}))
        (ax (P2 {A = A} {B = A ⇒ A} {C = A})))

  box-id-hilbert : ∀ {A : Formula} → S4 ⊢ₕ (□ A ⇒ □ A)
  box-id-hilbert {A} =
    MP
      (NEC (id-hilbert {A = A}))
      (ax (AxK {A = A} {B = A}))

  box-id-sequent : ∀ {A : Formula} → [] ⊢ [ (□ A ⇒ □ A) ^ [] ]
  box-id-sequent = completeness box-id-hilbert
