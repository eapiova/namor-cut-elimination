{-# OPTIONS #-}

open import NAMOR.Final.Syntax using (Logic; K; D; T; K4; D4; S4; S4dot2; S5)

module NAMOR.Final.CutElimination.CutElimination (M : Logic) where

open import Cubical.Foundations.Prelude
  using (Type; _≡_; refl; sym; cong; cong₂; subst; _∙_)
open import Cubical.Data.Nat using (ℕ; zero; suc; max)
open import Cubical.Data.Nat.Order
  using (_≤_; _<_; ≤-refl; ≤-trans; zero-≤; ≤0→≡0; suc-≤-suc;
         ¬-<-zero; <-weaken; pred-≤-pred)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd)
open import Cubical.Data.List using (_++_; [_])
open import Cubical.Data.List.Properties using (++-unit-r)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Empty renaming (rec to ⊥-rec) using (⊥)
open import Cubical.Induction.WellFounded using (Acc; acc)

open import NAMOR.Final.Syntax hiding (Logic; Not)
open import NAMOR.Final.System M
open import NAMOR.Final.Structural M using (structural)
open import NAMOR.Final.CutElimination.Defs M
  using (degree; δ; isCutFree; leq-max-1; leq-max-2; leq-max-2-1; leq-max-2-2;
         inv-s≤s)
open import NAMOR.Final.CutElimination.Base M
  using (structural-preserves-δ; cut-sub-left; cut-sub-right;
         pf-++; pf-singleton-eq)
open import NAMOR.Final.CutElimination.Mix M using (MixAPI; mix)

------------------------------------------------------------------------
-- Well-founded recursion on ℕ (<)

private
  acc≤ : (n : ℕ) → (m : ℕ) → m ≤ n → Acc _<_ m
  acc≤ n zero _ = acc λ k k<0 → ⊥-rec (¬-<-zero k<0)
  acc≤ zero (suc m) sm≤0 = ⊥-rec (¬-<-zero sm≤0)
  acc≤ (suc n) (suc m) sm≤sn =
    acc λ k k<sm →
      acc≤ n k (≤-trans (pred-≤-pred k<sm) (pred-≤-pred sm≤sn))

  <-wf : (n : ℕ) → Acc _<_ n
  <-wf n = acc λ m m<n → acc≤ n m (<-weaken m<n)

  n<sn : ∀ {n} → n < suc n
  n<sn {n} = suc-≤-suc ≤-refl

  max-zero : ∀ {a b} → a ≡ zero → b ≡ zero → max a b ≡ zero
  max-zero {a} {b} pa pb =
    subst (λ x → max x b ≡ zero) (sym pa)
      (subst (λ y → max zero y ≡ zero) (sym pb) refl)

  cutConstraint-lift-gen :
    (m : Logic)
    → ∀ {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {A : Formula} {α : Position}
    → cutConstraint m A α Γ₁ Γ₂ Δ₁ Δ₂
    → cutConstraint m A α
        Γ₁ (Γ₂ ++ [ (A ^ α) ]) ([ (A ^ α) ] ++ Δ₁) Δ₂
  cutConstraint-lift-gen K {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {α} c with c
  ... | inl w =
    let
      eqLrem : (([ (A ^ α) ] ++ Δ₁) -pf (A ^ α))
            ≡ (Δ₁ -pf (A ^ α))
      eqLrem =
        pf-++ (A ^ α) [ (A ^ α) ] Δ₁
        ∙ cong (_++ (Δ₁ -pf (A ^ α)))
            (pf-singleton-eq {φ = (A ^ α)} {ψ = (A ^ α)} refl)

      eqL : Γ₁ ++ (([ (A ^ α) ] ++ Δ₁) -pf (A ^ α))
          ≡ Γ₁ ++ (Δ₁ -pf (A ^ α))
      eqL = cong (Γ₁ ++_) eqLrem
    in inl (subst (α ∈Init_) (sym eqL) w)
  ... | inr w =
    let
      eqRem : ((Γ₂ ++ [ (A ^ α) ]) -pf (A ^ α))
            ≡ (Γ₂ -pf (A ^ α))
      eqRem =
        pf-++ (A ^ α) Γ₂ [ (A ^ α) ]
        ∙ cong ((Γ₂ -pf (A ^ α)) ++_)
            (pf-singleton-eq {φ = (A ^ α)} {ψ = (A ^ α)} refl)
        ∙ ++-unit-r (Γ₂ -pf (A ^ α))

      eqR : (((Γ₂ ++ [ (A ^ α) ]) -pf (A ^ α)) ++ Δ₂)
          ≡ ((Γ₂ -pf (A ^ α)) ++ Δ₂)
      eqR = cong (_++ Δ₂) eqRem
    in inr (subst (α ∈Init_) (sym eqR) w)
  cutConstraint-lift-gen D c = tt
  cutConstraint-lift-gen T c = tt
  cutConstraint-lift-gen K4 {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {α} c with c
  ... | inl w =
    let
      eqLrem : (([ (A ^ α) ] ++ Δ₁) -pf (A ^ α))
            ≡ (Δ₁ -pf (A ^ α))
      eqLrem =
        pf-++ (A ^ α) [ (A ^ α) ] Δ₁
        ∙ cong (_++ (Δ₁ -pf (A ^ α)))
            (pf-singleton-eq {φ = (A ^ α)} {ψ = (A ^ α)} refl)

      eqL : Γ₁ ++ (([ (A ^ α) ] ++ Δ₁) -pf (A ^ α))
          ≡ Γ₁ ++ (Δ₁ -pf (A ^ α))
      eqL = cong (Γ₁ ++_) eqLrem
    in inl (subst (α ∈Init_) (sym eqL) w)
  ... | inr w =
    let
      eqRem : ((Γ₂ ++ [ (A ^ α) ]) -pf (A ^ α))
            ≡ (Γ₂ -pf (A ^ α))
      eqRem =
        pf-++ (A ^ α) Γ₂ [ (A ^ α) ]
        ∙ cong ((Γ₂ -pf (A ^ α)) ++_)
            (pf-singleton-eq {φ = (A ^ α)} {ψ = (A ^ α)} refl)
        ∙ ++-unit-r (Γ₂ -pf (A ^ α))

      eqR : (((Γ₂ ++ [ (A ^ α) ]) -pf (A ^ α)) ++ Δ₂)
          ≡ ((Γ₂ -pf (A ^ α)) ++ Δ₂)
      eqR = cong (_++ Δ₂) eqRem
    in inr (subst (α ∈Init_) (sym eqR) w)
  cutConstraint-lift-gen D4 c = tt
  cutConstraint-lift-gen S4 c = tt
  cutConstraint-lift-gen S4dot2 c = tt
  cutConstraint-lift-gen S5 c = tt

  cutConstraint-lift :
    ∀ {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {A : Formula} {α : Position}
    → cutConstraint M A α Γ₁ Γ₂ Δ₁ Δ₂
    → cutConstraint M A α
        Γ₁ (Γ₂ ++ [ (A ^ α) ]) ([ (A ^ α) ] ++ Δ₁) Δ₂
  cutConstraint-lift = cutConstraint-lift-gen M

------------------------------------------------------------------------
-- Main theorem (parameterized by MixAPI)

-- %<*cutElimWith>
CutEliminationWith : MixAPI → {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → Σ (Γ ⊢ Δ) isCutFree
CutEliminationWith mix Π = cutElim Π (δ Π) ≤-refl (<-wf (δ Π))
-- %</cutElimWith>
  where
    -- %<*cutElimCore>
    cutElim : {Γ Δ : Ctx}
      → (Π : Γ ⊢ Δ) → (n : ℕ) → δ Π ≤ n → Acc _<_ n
      → Σ (Γ ⊢ Δ) isCutFree

    -- Base: δ Π = 0
    cutElim Π zero δ≤0 _ = Π , ≤0→≡0 δ≤0

    -- Axiom
    cutElim Ax (suc n) _ _ = Ax , refl

    -- Cut: recurse on premises, mix, recurse on mixed proof at smaller bound
    cutElim
      (Cut {A = A} {α = α} {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ₁ = Δ₁} {Δ₂ = Δ₂}
        c Π₁ Π₂)
      (suc n) δ≤sn (acc recAcc) =
      let
        degA≤n : degree A ≤ n
        degA≤n = inv-s≤s
          (leq-max-1 (suc (degree A)) (max (δ Π₁) (δ Π₂)) (suc n) δ≤sn)

        δΠ₁≤sn : δ Π₁ ≤ suc n
        δΠ₁≤sn = leq-max-2-1 (suc (degree A)) (δ Π₁) (δ Π₂) (suc n) δ≤sn

        δΠ₂≤sn : δ Π₂ ≤ suc n
        δΠ₂≤sn = leq-max-2-2 (suc (degree A)) (δ Π₁) (δ Π₂) (suc n) δ≤sn

        (Π₁* , cf₁) = cutElim Π₁ (suc n) δΠ₁≤sn (acc recAcc)
        (Π₂* , cf₂) = cutElim Π₂ (suc n) δΠ₂≤sn (acc recAcc)

        δΠ₁*≤degA : δ Π₁* ≤ degree A
        δΠ₁*≤degA = subst (λ x → x ≤ degree A) (sym cf₁) zero-≤

        δΠ₂*≤degA : δ Π₂* ≤ degree A
        δΠ₂*≤degA = subst (λ x → x ≤ degree A) (sym cf₂) zero-≤

        (Π₀ , δΠ₀≤degA) =
          mix (degree A) refl Π₁* Π₂* δΠ₁*≤degA δΠ₂*≤degA
            (cutConstraint-lift c)

        δΠ₀≤n : δ Π₀ ≤ n
        δΠ₀≤n = ≤-trans δΠ₀≤degA degA≤n

        (Π* , cf*) = cutElim Π₀ n δΠ₀≤n (recAcc n n<sn)

        Π** : (Γ₁ ++ Γ₂) ⊢ (Δ₁ ++ Δ₂)
        Π** = structural
          (cut-sub-left Γ₁ Γ₂ A α)
          (cut-sub-right Δ₁ Δ₂ A α)
          Π*

        cf** : isCutFree Π**
        cf** = structural-preserves-δ _ _ Π* ∙ cf*
      in Π** , cf**
    -- %</cutElimCore>

    -- Unary structural/propositional/modal cases
    cutElim (WeakenL Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in WeakenL Π* , cf*
    cutElim (WeakenR Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in WeakenR Π* , cf*
    cutElim (ContractL Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in ContractL Π* , cf*
    cutElim (ContractR Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in ContractR Π* , cf*
    cutElim (ExchangeL Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in ExchangeL Π* , cf*
    cutElim (ExchangeR Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in ExchangeR Π* , cf*
    cutElim (NotL Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in NotL Π* , cf*
    cutElim (NotR Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in NotR Π* , cf*
    cutElim (AndL1 Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in AndL1 Π* , cf*
    cutElim (AndL2 Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in AndL2 Π* , cf*
    cutElim (OrR1 Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in OrR1 Π* , cf*
    cutElim (OrR2 Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in OrR2 Π* , cf*
    cutElim (ImpR Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in ImpR Π* , cf*
    cutElim (BoxL c Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in BoxL c Π* , cf*
    cutElim (BoxR fr Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in BoxR fr Π* , cf*
    cutElim (DiaL fr Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in DiaL fr Π* , cf*
    cutElim (DiaR c Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in DiaR c Π* , cf*

    -- Binary non-cut rules
    cutElim (AndR Π₁ Π₂) (suc n) δ≤sn wf =
      let
        δΠ₁≤sn = leq-max-1 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        δΠ₂≤sn = leq-max-2 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        (Π₁* , cf₁) = cutElim Π₁ (suc n) δΠ₁≤sn wf
        (Π₂* , cf₂) = cutElim Π₂ (suc n) δΠ₂≤sn wf
      in AndR Π₁* Π₂* , (cong₂ max cf₁ cf₂ ∙ refl)

    cutElim (OrL Π₁ Π₂) (suc n) δ≤sn wf =
      let
        δΠ₁≤sn = leq-max-1 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        δΠ₂≤sn = leq-max-2 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        (Π₁* , cf₁) = cutElim Π₁ (suc n) δΠ₁≤sn wf
        (Π₂* , cf₂) = cutElim Π₂ (suc n) δΠ₂≤sn wf
      in OrL Π₁* Π₂* , (cong₂ max cf₁ cf₂ ∙ refl)

    cutElim (ImpL Π₁ Π₂) (suc n) δ≤sn wf =
      let
        δΠ₁≤sn = leq-max-1 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        δΠ₂≤sn = leq-max-2 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        (Π₁* , cf₁) = cutElim Π₁ (suc n) δΠ₁≤sn wf
        (Π₂* , cf₂) = cutElim Π₂ (suc n) δΠ₂≤sn wf
      in ImpL Π₁* Π₂* , (cong₂ max cf₁ cf₂ ∙ refl)

-- Backwards-compatible alias until concrete `mix : MixAPI` is exported.
CutElimination : MixAPI → {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → Σ (Γ ⊢ Δ) isCutFree
CutElimination = CutEliminationWith

-- Standalone cut elimination using the concrete mix
CutElim : {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → Σ (Γ ⊢ Δ) isCutFree
CutElim = CutEliminationWith mix

-- Projections
cutFreeProof : MixAPI → {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → Γ ⊢ Δ
cutFreeProof mix Π = fst (CutEliminationWith mix Π)

cutFreeProof-isCutFree : (mix : MixAPI) → {Γ Δ : Ctx}
  → (Π : Γ ⊢ Δ) → isCutFree (cutFreeProof mix Π)
cutFreeProof-isCutFree mix Π = snd (CutEliminationWith mix Π)
