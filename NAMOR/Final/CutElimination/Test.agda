{-# OPTIONS #-}

module NAMOR.Final.CutElimination.Test where

open import Cubical.Foundations.Prelude using (_≡_; refl)
open import Cubical.Data.Sigma using (Σ; _,_)
open import Cubical.Data.List using ([]; [_])
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (tt)

open import NAMOR.List.Any using (here)
open import NAMOR.List.Prefix using (⊑-refl)
open import NAMOR.Final.Syntax

private
  atom0 : Formula
  atom0 = atom 0

  pos0 : Position
  pos0 = []

  atom0at0 : PFormula
  atom0at0 = atom0 ^ pos0

  selfInit : pos0 ∈Init [ atom0at0 ]
  selfInit = atom0at0 , (here refl , ⊑-refl pos0)

module KSmoke where
  open import NAMOR.Final.System K
  open import NAMOR.Final.CutElimination.Mix K using (MixAPI)
  open import NAMOR.Final.CutElimination.Defs K using (isCutFree)
  open import NAMOR.Final.CutElimination.CutElimination K using (CutEliminationWith)

  cutWitness-inl : cutConstraint K atom0 pos0 [ atom0at0 ] [] [] [ atom0at0 ]
  cutWitness-inl = inl selfInit

  cutWitness-inr : cutConstraint K atom0 pos0 [ atom0at0 ] [] [] [ atom0at0 ]
  cutWitness-inr = inr selfInit

  cutProof-inl : [ atom0at0 ] ⊢ [ atom0at0 ]
  cutProof-inl = Cut cutWitness-inl Ax Ax

  cutProof-inr : [ atom0at0 ] ⊢ [ atom0at0 ]
  cutProof-inr = Cut cutWitness-inr Ax Ax

  smoke-inl : (mix : MixAPI) → Σ ([ atom0at0 ] ⊢ [ atom0at0 ]) isCutFree
  smoke-inl mix = CutEliminationWith mix cutProof-inl

  smoke-inr : (mix : MixAPI) → Σ ([ atom0at0 ] ⊢ [ atom0at0 ]) isCutFree
  smoke-inr mix = CutEliminationWith mix cutProof-inr

module DSmoke where
  open import NAMOR.Final.System D
  open import NAMOR.Final.CutElimination.Mix D using (MixAPI)
  open import NAMOR.Final.CutElimination.Defs D using (isCutFree)
  open import NAMOR.Final.CutElimination.CutElimination D using (CutEliminationWith)

  cutProof : [ atom0at0 ] ⊢ [ atom0at0 ]
  cutProof = Cut tt Ax Ax

  smoke : (mix : MixAPI) → Σ ([ atom0at0 ] ⊢ [ atom0at0 ]) isCutFree
  smoke mix = CutEliminationWith mix cutProof

module TSmoke where
  open import NAMOR.Final.System T
  open import NAMOR.Final.CutElimination.Mix T using (MixAPI)
  open import NAMOR.Final.CutElimination.Defs T using (isCutFree)
  open import NAMOR.Final.CutElimination.CutElimination T using (CutEliminationWith)

  cutProof : [ atom0at0 ] ⊢ [ atom0at0 ]
  cutProof = Cut tt Ax Ax

  smoke : (mix : MixAPI) → Σ ([ atom0at0 ] ⊢ [ atom0at0 ]) isCutFree
  smoke mix = CutEliminationWith mix cutProof

module K4Smoke where
  open import NAMOR.Final.System K4
  open import NAMOR.Final.CutElimination.Mix K4 using (MixAPI)
  open import NAMOR.Final.CutElimination.Defs K4 using (isCutFree)
  open import NAMOR.Final.CutElimination.CutElimination K4 using (CutEliminationWith)

  cutWitness-inl : cutConstraint K4 atom0 pos0 [ atom0at0 ] [] [] [ atom0at0 ]
  cutWitness-inl = inl selfInit

  cutWitness-inr : cutConstraint K4 atom0 pos0 [ atom0at0 ] [] [] [ atom0at0 ]
  cutWitness-inr = inr selfInit

  cutProof-inl : [ atom0at0 ] ⊢ [ atom0at0 ]
  cutProof-inl = Cut cutWitness-inl Ax Ax

  cutProof-inr : [ atom0at0 ] ⊢ [ atom0at0 ]
  cutProof-inr = Cut cutWitness-inr Ax Ax

  smoke-inl : (mix : MixAPI) → Σ ([ atom0at0 ] ⊢ [ atom0at0 ]) isCutFree
  smoke-inl mix = CutEliminationWith mix cutProof-inl

  smoke-inr : (mix : MixAPI) → Σ ([ atom0at0 ] ⊢ [ atom0at0 ]) isCutFree
  smoke-inr mix = CutEliminationWith mix cutProof-inr

module D4Smoke where
  open import NAMOR.Final.System D4
  open import NAMOR.Final.CutElimination.Mix D4 using (MixAPI)
  open import NAMOR.Final.CutElimination.Defs D4 using (isCutFree)
  open import NAMOR.Final.CutElimination.CutElimination D4 using (CutEliminationWith)

  cutProof : [ atom0at0 ] ⊢ [ atom0at0 ]
  cutProof = Cut tt Ax Ax

  smoke : (mix : MixAPI) → Σ ([ atom0at0 ] ⊢ [ atom0at0 ]) isCutFree
  smoke mix = CutEliminationWith mix cutProof

module S4Smoke where
  open import NAMOR.Final.System S4
  open import NAMOR.Final.CutElimination.Mix S4 using (MixAPI)
  open import NAMOR.Final.CutElimination.Defs S4 using (isCutFree)
  open import NAMOR.Final.CutElimination.CutElimination S4 using (CutEliminationWith)

  cutProof : [ atom0at0 ] ⊢ [ atom0at0 ]
  cutProof = Cut tt Ax Ax

  smoke : (mix : MixAPI) → Σ ([ atom0at0 ] ⊢ [ atom0at0 ]) isCutFree
  smoke mix = CutEliminationWith mix cutProof

module S4dot2Smoke where
  open import NAMOR.Final.System S4dot2
  open import NAMOR.Final.CutElimination.Mix S4dot2 using (MixAPI)
  open import NAMOR.Final.CutElimination.Defs S4dot2 using (isCutFree)
  open import NAMOR.Final.CutElimination.CutElimination S4dot2 using (CutEliminationWith)

  cutProof : [ atom0at0 ] ⊢ [ atom0at0 ]
  cutProof = Cut tt Ax Ax

  smoke : (mix : MixAPI) → Σ ([ atom0at0 ] ⊢ [ atom0at0 ]) isCutFree
  smoke mix = CutEliminationWith mix cutProof

module S5Smoke where
  open import NAMOR.Final.System S5
  open import NAMOR.Final.CutElimination.Mix S5 using (MixAPI)
  open import NAMOR.Final.CutElimination.Defs S5 using (isCutFree)
  open import NAMOR.Final.CutElimination.CutElimination S5 using (CutEliminationWith)

  cutProof : [ atom0at0 ] ⊢ [ atom0at0 ]
  cutProof = Cut tt Ax Ax

  smoke : (mix : MixAPI) → Σ ([ atom0at0 ] ⊢ [ atom0at0 ]) isCutFree
  smoke mix = CutEliminationWith mix cutProof
