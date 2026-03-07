{-# OPTIONS --safe #-}

open import NAMOR.Final.Syntax using (Logic)

module NAMOR.Final.CutElimination.Defs (M : Logic) where

open import Cubical.Foundations.Prelude
  using (Type; _≡_; refl; sym; cong; subst; J; substRefl; _∙_)
open import Agda.Primitive using (Level)
open import Cubical.Data.Empty renaming (rec to emptyRec) using (⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.List using (List; _∷_; []; _++_)
open import Cubical.Data.Sigma using (Σ; _,_)
open import Cubical.Relation.Nullary renaming (¬_ to Neg)
open import Cubical.Data.Nat using (ℕ; max; _+_; suc; snotz; zero; predℕ)
open import Cubical.Data.Nat.Order
  using (_≤_; ≤-refl; ≤-trans; left-≤-max; right-≤-max;
         ≤0→≡0; _<_; suc-≤-suc; pred-≤-pred)
open import Cubical.Data.Nat.Properties using (+-zero; +-suc; maxSuc)
open import Cubical.Data.Unit using (Unit; tt)

open import NAMOR.List.Membership using (_∈_; ∈-++⁻)
open import NAMOR.Final.Syntax using (Logic; Formula; atom; bot; _⇒_; And; Or; Not; □_; ♢_; Ctx)
open import NAMOR.Final.System M

-- Definition: Degree of a formula
-- %<*degree>
degree : Formula → ℕ
degree (atom _) = 0
degree bot      = 0
degree (A ⇒ B)  = suc (max (degree A) (degree B))
degree (And A B) = suc (max (degree A) (degree B))
degree (Or A B)  = suc (max (degree A) (degree B))
degree (Not A)   = suc (degree A)
degree (□ A)     = suc (degree A)
degree (♢ A)     = suc (degree A)
-- %</degree>

-- Definition: Height of a derivation
-- %<*heightDef>
height : ∀ {Γ Δ} → (Γ ⊢ Δ) → ℕ
height Ax               = 0
height (Cut _ p1 p2)    = max (height p1) (height p2) + 1
height (WeakenL p)      = height p + 1
height (WeakenR p)      = height p + 1
height (ContractL p)    = height p + 1
height (ContractR p)    = height p + 1
height (ExchangeL p)    = height p + 1
height (ExchangeR p)    = height p + 1
height (NotL p)         = height p + 1
height (NotR p)         = height p + 1
height (AndL1 p)        = height p + 1
height (AndL2 p)        = height p + 1
height (AndR p1 p2)     = max (height p1) (height p2) + 1
height (OrL p1 p2)      = max (height p1) (height p2) + 1
height (OrR1 p)         = height p + 1
height (OrR2 p)         = height p + 1
height (ImpL p1 p2)     = max (height p1) (height p2) + 1
height (ImpR p)         = height p + 1
height (BoxL _ p)       = height p + 1
height (BoxR _ p)       = height p + 1
height (DiaL _ p)       = height p + 1
height (DiaR _ p)       = height p + 1
-- %</heightDef>

-- Transport preserves height
height-subst : ∀ {A : Type} {P : A → Ctx} {Q : A → Ctx} {x y : A}
               (eq : x ≡ y) (Π : P x ⊢ Q x)
             → height (subst (λ a → P a ⊢ Q a) eq Π) ≡ height Π
height-subst {A} {P} {Q} {x} {y} eq Π =
  J (λ y' eq' → height (subst (λ a → P a ⊢ Q a) eq' Π) ≡ height Π)
    (cong height (substRefl {B = λ a → P a ⊢ Q a} Π))
    eq

height-subst-Γ : ∀ {A : Type} {P : A → Ctx} {Δ : Ctx} {x y : A}
                 (eq : x ≡ y) (Π : P x ⊢ Δ)
               → height (subst (λ a → P a ⊢ Δ) eq Π) ≡ height Π
height-subst-Γ {A} {P} {Δ} {x} {y} eq Π =
  J (λ y' eq' → height (subst (λ a → P a ⊢ Δ) eq' Π) ≡ height Π)
    (cong height (substRefl {B = λ a → P a ⊢ Δ} Π))
    eq

height-subst-Δ : ∀ {A : Type} {Γ : Ctx} {Q : A → Ctx} {x y : A}
                 (eq : x ≡ y) (Π : Γ ⊢ Q x)
               → height (subst (λ a → Γ ⊢ Q a) eq Π) ≡ height Π
height-subst-Δ {A} {Γ} {Q} {x} {y} eq Π =
  J (λ y' eq' → height (subst (λ a → Γ ⊢ Q a) eq' Π) ≡ height Π)
    (cong height (substRefl {B = λ a → Γ ⊢ Q a} Π))
    eq

-- Definition: Degree of a derivation (max degree of cut formulas)
-- %<*delta>
δ : ∀ {Γ Δ} → Γ ⊢ Δ → ℕ
δ Ax               = 0
δ (Cut {A = A} _ p1 p2) = max (suc (degree A)) (max (δ p1) (δ p2))
δ (WeakenL p)      = δ p
δ (WeakenR p)      = δ p
δ (ContractL p)    = δ p
δ (ContractR p)    = δ p
δ (ExchangeL p)    = δ p
δ (ExchangeR p)    = δ p
δ (NotL p)         = δ p
δ (NotR p)         = δ p
δ (AndL1 p)        = δ p
δ (AndL2 p)        = δ p
δ (AndR p1 p2)     = max (δ p1) (δ p2)
δ (OrL p1 p2)      = max (δ p1) (δ p2)
δ (OrR1 p)         = δ p
δ (OrR2 p)         = δ p
δ (ImpL p1 p2)     = max (δ p1) (δ p2)
δ (ImpR p)         = δ p
δ (BoxL _ p)       = δ p
δ (BoxR _ p)       = δ p
δ (DiaL _ p)       = δ p
δ (DiaR _ p)       = δ p
-- %</delta>

-- Transport preserves δ
δ-subst : ∀ {A : Type} {P : A → Ctx} {Q : A → Ctx} {x y : A}
          (eq : x ≡ y) (Π : P x ⊢ Q x)
        → δ (subst (λ a → P a ⊢ Q a) eq Π) ≡ δ Π
δ-subst {A} {P} {Q} {x} {y} eq Π =
  J (λ y' eq' → δ (subst (λ a → P a ⊢ Q a) eq' Π) ≡ δ Π)
    (cong δ (substRefl {B = λ a → P a ⊢ Q a} Π))
    eq

δ-subst-Γ : ∀ {A : Type} {P : A → Ctx} {Δ : Ctx} {x y : A}
            (eq : x ≡ y) (Π : P x ⊢ Δ)
          → δ (subst (λ a → P a ⊢ Δ) eq Π) ≡ δ Π
δ-subst-Γ {A} {P} {Δ} {x} {y} eq Π =
  J (λ y' eq' → δ (subst (λ a → P a ⊢ Δ) eq' Π) ≡ δ Π)
    (cong δ (substRefl {B = λ a → P a ⊢ Δ} Π))
    eq

δ-subst-Δ : ∀ {A : Type} {Γ : Ctx} {Q : A → Ctx} {x y : A}
            (eq : x ≡ y) (Π : Γ ⊢ Q x)
          → δ (subst (λ a → Γ ⊢ Q a) eq Π) ≡ δ Π
δ-subst-Δ {A} {Γ} {Q} {x} {y} eq Π =
  J (λ y' eq' → δ (subst (λ a → Γ ⊢ Q a) eq' Π) ≡ δ Π)
    (cong δ (substRefl {B = λ a → Γ ⊢ Q a} Π))
    eq

-- A derivation is cut-free iff δ = 0
-- %<*isCutFree>
isCutFree : {Γ Δ : Ctx} → Γ ⊢ Δ → Type
isCutFree p = δ p ≡ 0
-- %</isCutFree>

-- max decomposition helpers
leq-max-1 : ∀ m n k → max m n ≤ k → m ≤ k
leq-max-1 m n k p = ≤-trans left-≤-max p

leq-max-2 : ∀ m n k → max m n ≤ k → n ≤ k
leq-max-2 m n k p = ≤-trans (right-≤-max {n} {m}) p

leq-max-2-1 : ∀ m n k l → max m (max n k) ≤ l → n ≤ l
leq-max-2-1 m n k l p = leq-max-1 n k l (leq-max-2 m (max n k) l p)

leq-max-2-2 : ∀ m n k l → max m (max n k) ≤ l → k ≤ l
leq-max-2-2 m n k l p = leq-max-2 n k l (leq-max-2 m (max n k) l p)

≤-reflexive : ∀ {m n} → m ≡ n → m ≤ n
≤-reflexive {m} eq = subst (m ≤_) eq ≤-refl

_≢_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
x ≢ y = Neg (x ≡ y)

¬m<m : ∀ {m} → Neg (m < m)
¬m<m {zero} lt = snotz (≤0→≡0 lt)
¬m<m {suc m} lt = ¬m<m (pred-≤-pred lt)

<→≢ : ∀ {m n} → m < n → m ≢ n
<→≢ {m} {n} lt eq = ¬m<m (subst (λ k → k < n) eq lt)

z≤ : ∀ {n} → zero ≤ n
z≤ {n} = n , +-zero n

s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
s≤s {m} {n} (k , p) = k , (+-suc k m ∙ cong suc p)

inv-s≤s : ∀ {m n} → suc m ≤ suc n → m ≤ n
inv-s≤s {m} {n} (k , p) = k , (cong predℕ (sym (+-suc k m) ∙ p))

max-least : ∀ {m n k} → m ≤ k → n ≤ k → max m n ≤ k
max-least {zero} {n} {k} mk nk = nk
max-least {suc m} {zero} {k} mk nk = mk
max-least {suc m} {suc n} {zero} mk nk = emptyRec (snotz (≤0→≡0 mk))
max-least {suc m} {suc n} {suc k} mk nk =
  subst (λ z → z ≤ suc k) (sym (maxSuc {m} {n}))
    (s≤s (max-least (inv-s≤s mk) (inv-s≤s nk)))

-- Inspect helper for with-abstraction
data Inspect {ℓ} {A : Type ℓ} (x : A) : Type ℓ where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {ℓ} {A : Type ℓ} (x : A) → Inspect x
inspect x = it x refl

-- Membership split for concatenation
mem-++-split : ∀ {ℓ} {A : Type ℓ} {x : A} {xs ys : List A}
  → x ∈ xs ++ ys → (x ∈ xs) ⊎ (x ∈ ys)
mem-++-split {xs = xs} p = ∈-++⁻ xs p
