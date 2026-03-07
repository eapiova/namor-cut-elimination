{-# OPTIONS #-}

open import NAMOR.Final.Syntax using (Logic)

module NAMOR.Final.CutElimination.SubformulaProperty (M : Logic) where

open import Cubical.Foundations.Prelude
  using (Type; _≡_; refl; subst)
open import Cubical.Data.Nat using (ℕ; zero; suc; max)
open import Cubical.Data.Nat.Order
  using (_≤_; ≤0→≡0; left-≤-max; right-≤-max)
open import Cubical.Data.Nat.Properties using (snotz)
open import Cubical.Data.Sigma using (Σ; _,_; _×_)
open import Cubical.Data.List using (List; []; _∷_; _++_; [_])
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)

open import NAMOR.List.Any using (here; there)
open import NAMOR.List.Membership using (_∈_; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import NAMOR.Final.Syntax hiding (Logic)
open import NAMOR.Final.System M
open import NAMOR.Final.CutElimination.Defs M using (degree; δ; isCutFree)
open import NAMOR.Final.CutElimination.CutElimination M
  using (cutFreeProof; cutFreeProof-isCutFree)
open import NAMOR.Final.CutElimination.Mix M using (MixAPI)

private
  mem-++-l : {A : Type} {x : A} {xs ys : List A} → x ∈ xs → x ∈ xs ++ ys
  mem-++-l = ∈-++⁺ˡ

  mem-++-r : {A : Type} {x : A} (xs : List A) {ys : List A}
    → x ∈ ys → x ∈ xs ++ ys
  mem-++-r = ∈-++⁺ʳ

  mem-++-split : {A : Type} {x : A} (xs : List A) {ys : List A}
    → x ∈ xs ++ ys → (x ∈ xs) ⊎ (x ∈ ys)
  mem-++-split = ∈-++⁻

  singleton-eq : {A : Type} {x a : A} → x ∈ [ a ] → x ≡ a
  singleton-eq (here eq) = eq
  singleton-eq (there ())

  suc-not-≤-zero : {n : ℕ} → suc n ≤ zero → ⊥
  suc-not-≤-zero sn≤0 = snotz (≤0→≡0 sn≤0)

  suc-≤-max : (n m : ℕ) → suc n ≤ max (suc n) m
  suc-≤-max n m = left-≤-max {m = suc n} {n = m}

  max-suc-neq-zero : {n m : ℕ} → max (suc n) m ≡ zero → ⊥
  max-suc-neq-zero {n} {m} eq =
    suc-not-≤-zero (subst (suc n ≤_) eq (suc-≤-max n m))

-- %<*isSubformulaOf>
data _isSubformulaOf_ : PFormula → PFormula → Type where
  refl-sub : ∀ {A α} → (A ^ α) isSubformulaOf (A ^ α)
  Not-sub : ∀ {A α pf}
    → pf isSubformulaOf (A ^ α)
    → pf isSubformulaOf ((Not A) ^ α)
  And₁-sub : ∀ {A B α pf}
    → pf isSubformulaOf (A ^ α)
    → pf isSubformulaOf ((And A B) ^ α)
  And₂-sub : ∀ {A B α pf}
    → pf isSubformulaOf (B ^ α)
    → pf isSubformulaOf ((And A B) ^ α)
  Or₁-sub : ∀ {A B α pf}
    → pf isSubformulaOf (A ^ α)
    → pf isSubformulaOf ((Or A B) ^ α)
  Or₂-sub : ∀ {A B α pf}
    → pf isSubformulaOf (B ^ α)
    → pf isSubformulaOf ((Or A B) ^ α)
  Imp₁-sub : ∀ {A B α pf}
    → pf isSubformulaOf (A ^ α)
    → pf isSubformulaOf ((A ⇒ B) ^ α)
  Imp₂-sub : ∀ {A B α pf}
    → pf isSubformulaOf (B ^ α)
    → pf isSubformulaOf ((A ⇒ B) ^ α)
  □-sub : ∀ {A α β pf}
    → pf isSubformulaOf (A ^ β)
    → pf isSubformulaOf ((□ A) ^ α)
  ♢-sub : ∀ {A α β pf}
    → pf isSubformulaOf (A ^ β)
    → pf isSubformulaOf ((♢ A) ^ α)
-- %</isSubformulaOf>

_isSubformulaOfCtx_ : PFormula → Ctx → Type
pf isSubformulaOfCtx Γ =
  Σ PFormula λ qf → (qf ∈ Γ) × (pf isSubformulaOf qf)

isSubformulaOfSeq : PFormula → Ctx → Ctx → Type
isSubformulaOfSeq pf Γ Δ =
  (pf isSubformulaOfCtx Γ) ⊎ (pf isSubformulaOfCtx Δ)

allFormulasInProof : {Γ Δ : Ctx} → Γ ⊢ Δ → List PFormula
allFormulasInProof {Γ} {Δ} Ax = Γ ++ Δ
allFormulasInProof {Γ} {Δ} (Cut c Π₁ Π₂) =
  (Γ ++ Δ) ++ allFormulasInProof Π₁ ++ allFormulasInProof Π₂
allFormulasInProof {Γ} {Δ} (WeakenL Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (WeakenR Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (ContractL Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (ContractR Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (ExchangeL Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (ExchangeR Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (NotL Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (NotR Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (AndL1 Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (AndL2 Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (AndR Π₁ Π₂) =
  (Γ ++ Δ) ++ allFormulasInProof Π₁ ++ allFormulasInProof Π₂
allFormulasInProof {Γ} {Δ} (OrL Π₁ Π₂) =
  (Γ ++ Δ) ++ allFormulasInProof Π₁ ++ allFormulasInProof Π₂
allFormulasInProof {Γ} {Δ} (OrR1 Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (OrR2 Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (ImpL Π₁ Π₂) =
  (Γ ++ Δ) ++ allFormulasInProof Π₁ ++ allFormulasInProof Π₂
allFormulasInProof {Γ} {Δ} (ImpR Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (BoxL c Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (BoxR fr Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (DiaL fr Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (DiaR c Π) = (Γ ++ Δ) ++ allFormulasInProof Π

refl-subformula : (pf : PFormula) → pf isSubformulaOf pf
refl-subformula (A ^ α) = refl-sub

mem-gives-ctx-sub : {pf : PFormula} {Γ : Ctx}
  → pf ∈ Γ → pf isSubformulaOfCtx Γ
mem-gives-ctx-sub {pf} pfIn = pf , (pfIn , refl-subformula pf)

mem-gives-seq-sub-l : {pf : PFormula} {Γ Δ : Ctx}
  → pf ∈ Γ → isSubformulaOfSeq pf Γ Δ
mem-gives-seq-sub-l pfIn = inl (mem-gives-ctx-sub pfIn)

mem-gives-seq-sub-r : {pf : PFormula} {Γ Δ : Ctx}
  → pf ∈ Δ → isSubformulaOfSeq pf Γ Δ
mem-gives-seq-sub-r pfIn = inr (mem-gives-ctx-sub pfIn)

mem-gives-seq-sub : {pf : PFormula} {Γ Δ : Ctx}
  → pf ∈ Γ ++ Δ → isSubformulaOfSeq pf Γ Δ
mem-gives-seq-sub {pf} {Γ} {Δ} pfIn with mem-++-split Γ pfIn
... | inl pfInΓ = mem-gives-seq-sub-l pfInΓ
... | inr pfInΔ = mem-gives-seq-sub-r pfInΔ

------------------------------------------------------------------------
-- Structural rule preservation

seq-sub-WeakenL : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {α : Position}
  → isSubformulaOfSeq pf Γ Δ
  → isSubformulaOfSeq pf ((A ^ α) ∷ Γ) Δ
seq-sub-WeakenL (inl (qf , qfIn , sub)) = inl (qf , there qfIn , sub)
seq-sub-WeakenL (inr x) = inr x

seq-sub-WeakenR : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {α : Position}
  → isSubformulaOfSeq pf Γ Δ
  → isSubformulaOfSeq pf Γ ((A ^ α) ∷ Δ)
seq-sub-WeakenR (inl x) = inl x
seq-sub-WeakenR (inr (qf , qfIn , sub)) = inr (qf , there qfIn , sub)

contractL-mem : {qf : PFormula} {A : Formula} {α : Position} {Γ : Ctx}
  → qf ∈ ((A ^ α) ∷ (A ^ α) ∷ Γ) → qf ∈ ((A ^ α) ∷ Γ)
contractL-mem (here eq) = here eq
contractL-mem (there (here eq)) = here eq
contractL-mem (there (there qInΓ)) = there qInΓ

contractR-mem : {qf : PFormula} {A : Formula} {α : Position} {Δ : Ctx}
  → qf ∈ ((A ^ α) ∷ (A ^ α) ∷ Δ) → qf ∈ ((A ^ α) ∷ Δ)
contractR-mem (here eq) = here eq
contractR-mem (there (here eq)) = here eq
contractR-mem (there (there qInΔ)) = there qInΔ

seq-sub-ContractL : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {α : Position}
  → isSubformulaOfSeq pf ((A ^ α) ∷ (A ^ α) ∷ Γ) Δ
  → isSubformulaOfSeq pf ((A ^ α) ∷ Γ) Δ
seq-sub-ContractL (inl (qf , qfIn , sub)) =
  inl (qf , contractL-mem qfIn , sub)
seq-sub-ContractL (inr x) = inr x

seq-sub-ContractR : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {α : Position}
  → isSubformulaOfSeq pf Γ ((A ^ α) ∷ (A ^ α) ∷ Δ)
  → isSubformulaOfSeq pf Γ ((A ^ α) ∷ Δ)
seq-sub-ContractR (inl x) = inl x
seq-sub-ContractR (inr (qf , qfIn , sub)) =
  inr (qf , contractR-mem qfIn , sub)

exchangeL-mem : {qf c d : PFormula} {Γ₁ Γ₂ : Ctx}
  → qf ∈ (Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂)
  → qf ∈ (Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂)
exchangeL-mem {qf} {c} {d} {Γ₁} {Γ₂} qIn with mem-++-split Γ₁ qIn
... | inl qInΓ₁ = mem-++-l qInΓ₁
... | inr qInCDΓ₂ with mem-++-split [ c ] qInCDΓ₂
...   | inl qInC =
      mem-++-r Γ₁ (mem-++-r [ d ] (mem-++-l qInC))
...   | inr qInDΓ₂ with mem-++-split [ d ] qInDΓ₂
...     | inl qInd = mem-++-r Γ₁ (mem-++-l qInd)
...     | inr qInΓ₂ =
        mem-++-r Γ₁ (mem-++-r [ d ] (mem-++-r [ c ] qInΓ₂))

exchangeR-mem : {qf c d : PFormula} {Δ₁ Δ₂ : Ctx}
  → qf ∈ (Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂)
  → qf ∈ (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂)
exchangeR-mem {qf} {c} {d} {Δ₁} {Δ₂} qIn with mem-++-split Δ₁ qIn
... | inl qInΔ₁ = mem-++-l qInΔ₁
... | inr qInCDΔ₂ with mem-++-split [ c ] qInCDΔ₂
...   | inl qInC =
      mem-++-r Δ₁ (mem-++-r [ d ] (mem-++-l qInC))
...   | inr qInDΔ₂ with mem-++-split [ d ] qInDΔ₂
...     | inl qInd = mem-++-r Δ₁ (mem-++-l qInd)
...     | inr qInΔ₂ =
        mem-++-r Δ₁ (mem-++-r [ d ] (mem-++-r [ c ] qInΔ₂))

seq-sub-ExchangeL : {pf : PFormula} {Γ₁ Γ₂ Δ : Ctx} {c d : PFormula}
  → isSubformulaOfSeq pf (Γ₁ ++ [ c ] ++ [ d ] ++ Γ₂) Δ
  → isSubformulaOfSeq pf (Γ₁ ++ [ d ] ++ [ c ] ++ Γ₂) Δ
seq-sub-ExchangeL (inl (qf , qfIn , sub)) =
  inl (qf , exchangeL-mem qfIn , sub)
seq-sub-ExchangeL (inr x) = inr x

seq-sub-ExchangeR : {pf : PFormula} {Γ Δ₁ Δ₂ : Ctx} {c d : PFormula}
  → isSubformulaOfSeq pf Γ (Δ₁ ++ [ c ] ++ [ d ] ++ Δ₂)
  → isSubformulaOfSeq pf Γ (Δ₁ ++ [ d ] ++ [ c ] ++ Δ₂)
seq-sub-ExchangeR (inl x) = inl x
seq-sub-ExchangeR (inr (qf , qfIn , sub)) =
  inr (qf , exchangeR-mem qfIn , sub)

------------------------------------------------------------------------
-- Logical + modal rule preservation

seq-sub-NotL : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {α : Position}
  → isSubformulaOfSeq pf Γ ((A ^ α) ∷ Δ)
  → isSubformulaOfSeq pf ((Not A ^ α) ∷ Γ) Δ
seq-sub-NotL (inl (qf , qfIn , sub)) = inl (qf , there qfIn , sub)
seq-sub-NotL {pf} {Γ} {Δ} {A} {α} (inr (qf , qfIn , sub)) with qfIn
... | here eq =
  inl ((Not A ^ α) , here refl ,
      Not-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΔ = inr (qf , qInΔ , sub)

seq-sub-NotR : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {α : Position}
  → isSubformulaOfSeq pf ((A ^ α) ∷ Γ) Δ
  → isSubformulaOfSeq pf Γ ((Not A ^ α) ∷ Δ)
seq-sub-NotR (inr (qf , qfIn , sub)) = inr (qf , there qfIn , sub)
seq-sub-NotR {pf} {Γ} {Δ} {A} {α} (inl (qf , qfIn , sub)) with qfIn
... | here eq =
  inr ((Not A ^ α) , here refl ,
      Not-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΓ = inl (qf , qInΓ , sub)

seq-sub-AndL1 : {pf : PFormula} {Γ Δ : Ctx} {A B : Formula} {α : Position}
  → isSubformulaOfSeq pf ((A ^ α) ∷ Γ) Δ
  → isSubformulaOfSeq pf ((And A B ^ α) ∷ Γ) Δ
seq-sub-AndL1 (inr x) = inr x
seq-sub-AndL1 {pf} {Γ} {Δ} {A} {B} {α} (inl (qf , qfIn , sub)) with qfIn
... | here eq =
  inl ((And A B ^ α) , here refl ,
      And₁-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΓ = inl (qf , there qInΓ , sub)

seq-sub-AndL2 : {pf : PFormula} {Γ Δ : Ctx} {A B : Formula} {α : Position}
  → isSubformulaOfSeq pf ((B ^ α) ∷ Γ) Δ
  → isSubformulaOfSeq pf ((And A B ^ α) ∷ Γ) Δ
seq-sub-AndL2 (inr x) = inr x
seq-sub-AndL2 {pf} {Γ} {Δ} {A} {B} {α} (inl (qf , qfIn , sub)) with qfIn
... | here eq =
  inl ((And A B ^ α) , here refl ,
      And₂-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΓ = inl (qf , there qInΓ , sub)

seq-sub-OrR1 : {pf : PFormula} {Γ Δ : Ctx} {A B : Formula} {α : Position}
  → isSubformulaOfSeq pf Γ ((A ^ α) ∷ Δ)
  → isSubformulaOfSeq pf Γ ((Or A B ^ α) ∷ Δ)
seq-sub-OrR1 (inl x) = inl x
seq-sub-OrR1 {pf} {Γ} {Δ} {A} {B} {α} (inr (qf , qfIn , sub)) with qfIn
... | here eq =
  inr ((Or A B ^ α) , here refl ,
      Or₁-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΔ = inr (qf , there qInΔ , sub)

seq-sub-OrR2 : {pf : PFormula} {Γ Δ : Ctx} {A B : Formula} {α : Position}
  → isSubformulaOfSeq pf Γ ((B ^ α) ∷ Δ)
  → isSubformulaOfSeq pf Γ ((Or A B ^ α) ∷ Δ)
seq-sub-OrR2 (inl x) = inl x
seq-sub-OrR2 {pf} {Γ} {Δ} {A} {B} {α} (inr (qf , qfIn , sub)) with qfIn
... | here eq =
  inr ((Or A B ^ α) , here refl ,
      Or₂-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΔ = inr (qf , there qInΔ , sub)

seq-sub-ImpR : {pf : PFormula} {Γ Δ : Ctx} {A B : Formula} {α : Position}
  → isSubformulaOfSeq pf ((A ^ α) ∷ Γ) ((B ^ α) ∷ Δ)
  → isSubformulaOfSeq pf Γ ((A ⇒ B ^ α) ∷ Δ)
seq-sub-ImpR {pf} {Γ} {Δ} {A} {B} {α} (inl (qf , qfIn , sub)) with qfIn
... | here eq =
  inr ((A ⇒ B ^ α) , here refl ,
      Imp₁-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΓ = inl (qf , qInΓ , sub)
seq-sub-ImpR {pf} {Γ} {Δ} {A} {B} {α} (inr (qf , qfIn , sub)) with qfIn
... | here eq =
  inr ((A ⇒ B ^ α) , here refl ,
      Imp₂-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΔ = inr (qf , there qInΔ , sub)

seq-sub-BoxL : {pf : PFormula} {Γ Δ : Ctx}
  {A : Formula} {α β : Position}
  → isSubformulaOfSeq pf (Γ ++ [ (A ^ β) ]) Δ
  → isSubformulaOfSeq pf (Γ ++ [ (□ A ^ α) ]) Δ
seq-sub-BoxL (inr x) = inr x
seq-sub-BoxL {pf} {Γ} {Δ} {A} {α} {β} (inl (qf , qfIn , sub))
  with mem-++-split Γ qfIn
... | inl qInΓ = inl (qf , mem-++-l qInΓ , sub)
... | inr qInA =
  inl ((□ A ^ α) , mem-++-r Γ (here refl) ,
      □-sub (subst (λ z → pf isSubformulaOf z) (singleton-eq qInA) sub))

seq-sub-BoxR : {pf : PFormula} {Γ Δ : Ctx}
  {A : Formula} {α β : Position}
  → isSubformulaOfSeq pf Γ ([ (A ^ β) ] ++ Δ)
  → isSubformulaOfSeq pf Γ ([ (□ A ^ α) ] ++ Δ)
seq-sub-BoxR (inl x) = inl x
seq-sub-BoxR {pf} {Γ} {Δ} {A} {α} {β} (inr (qf , qfIn , sub)) with qfIn
... | here eq =
  inr ((□ A ^ α) , here refl ,
      □-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΔ = inr (qf , there qInΔ , sub)

seq-sub-DiaL : {pf : PFormula} {Γ Δ : Ctx}
  {A : Formula} {α β : Position}
  → isSubformulaOfSeq pf (Γ ++ [ (A ^ β) ]) Δ
  → isSubformulaOfSeq pf (Γ ++ [ (♢ A ^ α) ]) Δ
seq-sub-DiaL (inr x) = inr x
seq-sub-DiaL {pf} {Γ} {Δ} {A} {α} {β} (inl (qf , qfIn , sub))
  with mem-++-split Γ qfIn
... | inl qInΓ = inl (qf , mem-++-l qInΓ , sub)
... | inr qInA =
  inl ((♢ A ^ α) , mem-++-r Γ (here refl) ,
      ♢-sub (subst (λ z → pf isSubformulaOf z) (singleton-eq qInA) sub))

seq-sub-DiaR : {pf : PFormula} {Γ Δ : Ctx}
  {A : Formula} {α β : Position}
  → isSubformulaOfSeq pf Γ ([ (A ^ β) ] ++ Δ)
  → isSubformulaOfSeq pf Γ ([ (♢ A ^ α) ] ++ Δ)
seq-sub-DiaR (inl x) = inl x
seq-sub-DiaR {pf} {Γ} {Δ} {A} {α} {β} (inr (qf , qfIn , sub)) with qfIn
... | here eq =
  inr ((♢ A ^ α) , here refl ,
      ♢-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΔ = inr (qf , there qInΔ , sub)

seq-sub-AndR : {pf : PFormula}
  {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {A B : Formula} {α : Position}
  → isSubformulaOfSeq pf Γ₁ ((A ^ α) ∷ Δ₁)
    ⊎ isSubformulaOfSeq pf Γ₂ ((B ^ α) ∷ Δ₂)
  → isSubformulaOfSeq pf (Γ₁ ++ Γ₂) ((And A B ^ α) ∷ (Δ₁ ++ Δ₂))
seq-sub-AndR {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inl (inl (qf , qInΓ₁ , sub))) =
  inl (qf , mem-++-l qInΓ₁ , sub)
seq-sub-AndR {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inl (inr (qf , qInAΔ₁ , sub))) with qInAΔ₁
... | here eq =
  inr ((And A B ^ α) , here refl ,
      And₁-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΔ₁ = inr (qf , there (mem-++-l qInΔ₁) , sub)
seq-sub-AndR {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inr (inl (qf , qInΓ₂ , sub))) =
  inl (qf , mem-++-r Γ₁ qInΓ₂ , sub)
seq-sub-AndR {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inr (inr (qf , qInBΔ₂ , sub))) with qInBΔ₂
... | here eq =
  inr ((And A B ^ α) , here refl ,
      And₂-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΔ₂ = inr (qf , there (mem-++-r Δ₁ qInΔ₂) , sub)

seq-sub-OrL : {pf : PFormula}
  {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {A B : Formula} {α : Position}
  → isSubformulaOfSeq pf ((A ^ α) ∷ Γ₁) Δ₁
    ⊎ isSubformulaOfSeq pf ((B ^ α) ∷ Γ₂) Δ₂
  → isSubformulaOfSeq pf ((Or A B ^ α) ∷ (Γ₁ ++ Γ₂)) (Δ₁ ++ Δ₂)
seq-sub-OrL {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inl (inl (qf , qInAΓ₁ , sub))) with qInAΓ₁
... | here eq =
  inl ((Or A B ^ α) , here refl ,
      Or₁-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΓ₁ = inl (qf , there (mem-++-l qInΓ₁) , sub)
seq-sub-OrL {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inl (inr (qf , qInΔ₁ , sub))) =
  inr (qf , mem-++-l qInΔ₁ , sub)
seq-sub-OrL {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inr (inl (qf , qInBΓ₂ , sub))) with qInBΓ₂
... | here eq =
  inl ((Or A B ^ α) , here refl ,
      Or₂-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΓ₂ = inl (qf , there (mem-++-r Γ₁ qInΓ₂) , sub)
seq-sub-OrL {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inr (inr (qf , qInΔ₂ , sub))) =
  inr (qf , mem-++-r Δ₁ qInΔ₂ , sub)

seq-sub-ImpL : {pf : PFormula}
  {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {A B : Formula} {α : Position}
  → isSubformulaOfSeq pf Γ₁ ((A ^ α) ∷ Δ₁)
    ⊎ isSubformulaOfSeq pf ((B ^ α) ∷ Γ₂) Δ₂
  → isSubformulaOfSeq pf ((A ⇒ B ^ α) ∷ (Γ₁ ++ Γ₂)) (Δ₁ ++ Δ₂)
seq-sub-ImpL {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inl (inl (qf , qInΓ₁ , sub))) =
  inl (qf , there (mem-++-l qInΓ₁) , sub)
seq-sub-ImpL {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inl (inr (qf , qInAΔ₁ , sub))) with qInAΔ₁
... | here eq =
  inl ((A ⇒ B ^ α) , here refl ,
      Imp₁-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΔ₁ = inr (qf , mem-++-l qInΔ₁ , sub)
seq-sub-ImpL {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inr (inl (qf , qInBΓ₂ , sub))) with qInBΓ₂
... | here eq =
  inl ((A ⇒ B ^ α) , here refl ,
      Imp₂-sub (subst (λ z → pf isSubformulaOf z) eq sub))
... | there qInΓ₂ = inl (qf , there (mem-++-r Γ₁ qInΓ₂) , sub)
seq-sub-ImpL {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {α} (inr (inr (qf , qInΔ₂ , sub))) =
  inr (qf , mem-++-r Δ₁ qInΔ₂ , sub)

------------------------------------------------------------------------
-- Main theorem

-- %<*subformulaProp>
SubformulaProperty : {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → isCutFree Π
  → (pf : PFormula) → pf ∈ allFormulasInProof Π
  → isSubformulaOfSeq pf Γ Δ
SubformulaProperty Ax cf pf pfIn = mem-gives-seq-sub pfIn
-- %</subformulaProp>
SubformulaProperty (Cut {A = A} c Π₁ Π₂) cf pf pfIn =
  ⊥-rec (max-suc-neq-zero {n = degree A} {m = max (δ Π₁) (δ Π₂)} cf)
SubformulaProperty {Γ} {Δ}
  (WeakenL Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-WeakenL (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (WeakenR Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-WeakenR (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (ContractL Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-ContractL (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (ContractR Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-ContractR (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (ExchangeL Π) cf pf pfIn with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-ExchangeL (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (ExchangeR Π) cf pf pfIn with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-ExchangeR (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (NotL Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-NotL (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (NotR Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-NotR (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (AndL1 Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-AndL1 (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (AndL2 Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-AndL2 (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (AndR Π₁ Π₂) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub with mem-++-split (allFormulasInProof Π₁) pfInSub
...   | inl pfIn₁ =
      let
        cf₁ : isCutFree Π₁
        cf₁ = ≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁} {n = δ Π₂}))
      in seq-sub-AndR (inl (SubformulaProperty Π₁ cf₁ pf pfIn₁))
...   | inr pfIn₂ =
      let
        cf₂ : isCutFree Π₂
        cf₂ = ≤0→≡0 (subst (δ Π₂ ≤_) cf (right-≤-max {n = δ Π₂} {m = δ Π₁}))
      in seq-sub-AndR (inr (SubformulaProperty Π₂ cf₂ pf pfIn₂))
SubformulaProperty {Γ} {Δ}
  (OrL Π₁ Π₂) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub with mem-++-split (allFormulasInProof Π₁) pfInSub
...   | inl pfIn₁ =
      let
        cf₁ : isCutFree Π₁
        cf₁ = ≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁} {n = δ Π₂}))
      in seq-sub-OrL (inl (SubformulaProperty Π₁ cf₁ pf pfIn₁))
...   | inr pfIn₂ =
      let
        cf₂ : isCutFree Π₂
        cf₂ = ≤0→≡0 (subst (δ Π₂ ≤_) cf (right-≤-max {n = δ Π₂} {m = δ Π₁}))
      in seq-sub-OrL (inr (SubformulaProperty Π₂ cf₂ pf pfIn₂))
SubformulaProperty {Γ} {Δ}
  (OrR1 Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-OrR1 (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (OrR2 Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-OrR2 (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (ImpL Π₁ Π₂) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub with mem-++-split (allFormulasInProof Π₁) pfInSub
...   | inl pfIn₁ =
      let
        cf₁ : isCutFree Π₁
        cf₁ = ≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁} {n = δ Π₂}))
      in seq-sub-ImpL (inl (SubformulaProperty Π₁ cf₁ pf pfIn₁))
...   | inr pfIn₂ =
      let
        cf₂ : isCutFree Π₂
        cf₂ = ≤0→≡0 (subst (δ Π₂ ≤_) cf (right-≤-max {n = δ Π₂} {m = δ Π₁}))
      in seq-sub-ImpL (inr (SubformulaProperty Π₂ cf₂ pf pfIn₂))
SubformulaProperty {Γ} {Δ}
  (ImpR Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-ImpR (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (BoxL c Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-BoxL (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (BoxR fr Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-BoxR (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (DiaL fr Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-DiaL (SubformulaProperty Π cf pf pfInSub)
SubformulaProperty {Γ} {Δ}
  (DiaR c Π) cf pf pfIn
  with mem-++-split (Γ ++ Δ) pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub-DiaR (SubformulaProperty Π cf pf pfInSub)

SubformulaPropertyWith : (mix : MixAPI) → {Γ Δ : Ctx}
  → (Π : Γ ⊢ Δ) → (pf : PFormula)
  → pf ∈ allFormulasInProof (cutFreeProof mix Π)
  → isSubformulaOfSeq pf Γ Δ
SubformulaPropertyWith mix Π pf pfIn =
  SubformulaProperty (cutFreeProof mix Π) (cutFreeProof-isCutFree mix Π) pf pfIn
