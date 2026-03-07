{-# OPTIONS --safe #-}

open import NAMOR.Final.Syntax using (Logic)

module NAMOR.Final.Equivalence.HilbertCompleteness (M : Logic) where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List using (List; []; _∷_; _++_; [_])
open import Cubical.Data.List.Properties using (++-assoc; ++-unit-r)
open import Cubical.Data.Nat using (ℕ; zero; suc; znots; snotz)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary using (¬_)

open import NAMOR.List.Any using (Any; here; there; Any-++⁺ʳ)
open import NAMOR.List.Membership using (_∈_; _⊆_; ∈-here; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import NAMOR.List.Prefix
  using (_⊑_; ⊑-refl; ⊑-++; ⊑-trans)
  renaming ([] to ⊑[]; _∷_ to _⊑∷_)

open import NAMOR.Final.Syntax
open import NAMOR.Final.System M
open import NAMOR.Final.InitLemmas using (∉Init-++)
open import NAMOR.Final.Hilbert

private
  variable
    A B C : Formula
    α β : Position
    x y : Token

------------------------------------------------------------------------
-- Basic helpers

_≢_ : Token → Token → Type
u ≢ v = u ≡ v → ⊥

0≢1 : zero ≢ suc zero
0≢1 = znots

1≢0 : suc zero ≢ zero
1≢0 = snotz

subset-refl : ∀ {xs : List Token} → xs ⊆ xs
subset-refl m = m

subset-step : ∀ {a : Token} {xs ys : List Token}
  → xs ⊆ ys
  → xs ⊆ (a ∷ ys)
subset-step sub m = there (sub m)

subset-step-right : ∀ {xs : List Token} {u : Token}
  → xs ⊆ (xs ++ [ u ])
subset-step-right = ∈-++⁺ˡ

subset-step-step : ∀ {xs : List Token} {u v : Token}
  → xs ⊆ ((xs ++ [ u ]) ++ [ v ])
subset-step-step m = ∈-++⁺ˡ (∈-++⁺ˡ m)

subset-step1-into-step0-1 : ∀ {xs : List Token}
  → (xs ++ [ suc zero ]) ⊆ ((xs ++ [ zero ]) ++ [ suc zero ])
subset-step1-into-step0-1 {xs} m with ∈-++⁻ xs m
... | inl mxs = ∈-++⁺ˡ (∈-++⁺ˡ mxs)
... | inr m1 = ∈-++⁺ʳ (xs ++ [ zero ]) m1

¬step⊑self : ∀ {s : Position} {u : Token} → ((s ++ [ u ]) ⊑ s) → ⊥
¬step⊑self {s = []} {u} ()
¬step⊑self {s = _ ∷ s} {u} (_ ⊑∷ p) = ¬step⊑self {s = s} {u} p

¬step⊑step-diff : ∀ {s : Position} {u v : Token}
  → u ≢ v
  → ((s ++ [ u ]) ⊑ (s ++ [ v ]))
  → ⊥
¬step⊑step-diff {s = []} {u} {v} u≢v (p ⊑∷ ⊑[]) = u≢v p
¬step⊑step-diff {s = _ ∷ s} {u} {v} u≢v (_ ⊑∷ p) =
  ¬step⊑step-diff {s = s} {u} {v} u≢v p

¬step-step⊑self : ∀ {s : Position} {u v : Token}
  → (((s ++ [ u ]) ++ [ v ]) ⊑ s)
  → ⊥
¬step-step⊑self {s} {u} {v} p =
  ¬step⊑self {s = s} {u = u}
    (⊑-trans (⊑-++ (s ++ [ u ]) [ v ]) p)

¬eq-step : ∀ {s : Position} {u : Token}
  → s ≡ (s ++ [ u ])
  → ⊥
¬eq-step {s} {u} eq =
  ¬step⊑self {s = s} {u = u}
    (subst ((s ++ [ u ]) ⊑_) (sym eq) (⊑-refl (s ++ [ u ])))

¬eq-step-step : ∀ {s : Position} {u v : Token}
  → s ≡ ((s ++ [ u ]) ++ [ v ])
  → ⊥
¬eq-step-step {s} {u} {v} eq =
  ¬step⊑self {s = s} {u = u}
    (subst ((s ++ [ u ]) ⊑_) (sym eq) (⊑-++ (s ++ [ u ]) [ v ]))

strict-step : ∀ {s : Position} {u : Token}
  → s ⊏ (s ++ [ u ])
strict-step {s} {u} = (⊑-++ s [ u ]) , ¬eq-step

strict-step-step : ∀ {s : Position} {u v : Token}
  → s ⊏ ((s ++ [ u ]) ++ [ v ])
strict-step-step {s} {u} {v} =
  (⊑-trans (⊑-++ s [ u ]) (⊑-++ (s ++ [ u ]) [ v ])) , ¬eq-step-step

prefix-step-step : ∀ {s : Position} {u v : Token}
  → s ⊑ ((s ++ [ u ]) ++ [ v ])
prefix-step-step {s} {u} {v} =
  ⊑-trans (⊑-++ s [ u ]) (⊑-++ (s ++ [ u ]) [ v ])

step∉Init[] : ∀ {s : Position} {u : Token} → (s ++ [ u ]) ∉Init []
step∉Init[] (_ , () , _)

step∉Init-single : ∀ {F : Formula} {s : Position} {u : Token}
  → (s ++ [ u ]) ∉Init [ F ^ s ]
step∉Init-single {s = s} {u} (_ , here eq , p) =
  ¬step⊑self {s = s} {u = u}
    (subst ((s ++ [ u ]) ⊑_) (cong PFormula.pos eq) p)
step∉Init-single (_ , there () , _)

stepStep∉Init-single : ∀ {F : Formula} {s : Position} {u v : Token}
  → ((s ++ [ u ]) ++ [ v ]) ∉Init [ F ^ s ]
stepStep∉Init-single {s = s} {u} {v} (_ , here eq , p) =
  ¬step-step⊑self {s = s} {u = u} {v = v}
    (subst (((s ++ [ u ]) ++ [ v ]) ⊑_) (cong PFormula.pos eq) p)
stepStep∉Init-single (_ , there () , _)

stepDiff∉Init-single : ∀ {F : Formula} {s : Position} {u v : Token}
  → u ≢ v
  → (s ++ [ u ]) ∉Init [ F ^ (s ++ [ v ]) ]
stepDiff∉Init-single {s = s} {u} {v} u≢v (_ , here eq , p) =
  ¬step⊑step-diff {s = s} {u = u} {v = v} u≢v
    (subst ((s ++ [ u ]) ⊑_) (cong PFormula.pos eq) p)
stepDiff∉Init-single u≢v (_ , there () , _)

has-singleton : ∀ {F : Formula} {s : Position} → [ F ^ s ] has s
has-singleton {s = s} = here ([] , [] , sym (++-unit-r s))

has-head : ∀ {F : Formula} {s : Position} {Γ : Ctx}
  → ((F ^ s) ∷ Γ) has s
has-head {s = s} = here ([] , [] , sym (++-unit-r s))

has-append-right-singleton : ∀ {Γ : Ctx} {F : Formula} {s : Position}
  → (Γ ++ [ F ^ s ]) has s
has-append-right-singleton {Γ = Γ} = Any-++⁺ʳ Γ has-singleton

------------------------------------------------------------------------
-- Constraint witnesses

modalConstraint-step-gen : (m : Logic)
  → ∀ {s : Position} {u : Token} {Γ Δ : Ctx}
  → ((Γ ++ Δ) has (s ++ [ u ]))
  → modalConstraint m s (s ++ [ u ]) Γ Δ
modalConstraint-step-gen K {u = u} h = (u , refl) , h
modalConstraint-step-gen D {u = u} h = u , refl
modalConstraint-step-gen T {u = u} h = inr (u , refl)
modalConstraint-step-gen K4 h = strict-step , h
modalConstraint-step-gen D4 h = strict-step
modalConstraint-step-gen S4 {s = s} {u = u} h = ⊑-++ s [ u ]
modalConstraint-step-gen S4dot2 h = subset-step-right
modalConstraint-step-gen S5 h = tt

modalConstraint-step : ∀ {s : Position} {u : Token} {Γ Δ : Ctx}
  → ((Γ ++ Δ) has (s ++ [ u ]))
  → modalConstraint M s (s ++ [ u ]) Γ Δ
modalConstraint-step = modalConstraint-step-gen M

cutWitness-MP-gen : (m : Logic)
  → ∀ {A B : Formula} {s : Position}
  → cutConstraint m (A ⇒ B) s [] [] [] [ B ^ s ]
cutWitness-MP-gen K {B = B} {s = s} = inr ((B ^ s) , ∈-here , ⊑-refl s)
cutWitness-MP-gen D = tt
cutWitness-MP-gen T = tt
cutWitness-MP-gen K4 {B = B} {s = s} = inr ((B ^ s) , ∈-here , ⊑-refl s)
cutWitness-MP-gen D4 = tt
cutWitness-MP-gen S4 = tt
cutWitness-MP-gen S4dot2 = tt
cutWitness-MP-gen S5 = tt

cutWitness-MP : ∀ {A B : Formula} {s : Position}
  → cutConstraint M (A ⇒ B) s [] [] [] [ B ^ s ]
cutWitness-MP = cutWitness-MP-gen M

------------------------------------------------------------------------
-- Axiom derivations at arbitrary position

derive-P1 : ∀ {A B : Formula} {s : Position}
  → [] ⊢ [ (A ⇒ (B ⇒ A)) ^ s ]
derive-P1 {A} {B} {s} =
  ImpR (ImpR (WeakenL {A = B} {α = s} (Ax {A = A} {α = s})))

derive-P2 : ∀ {A B C : Formula} {s : Position}
  → [] ⊢ [ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) ^ s ]
derive-P2 {A} {B} {C} {s} =
  let
    p : PFormula
    p = (A ⇒ (B ⇒ C)) ^ s

    q : PFormula
    q = (A ⇒ B) ^ s

    a : PFormula
    a = A ^ s

    b : PFormula
    b = B ^ s

    c : PFormula
    c = C ^ s

    bc : PFormula
    bc = (B ⇒ C) ^ s

    bc⊢c : (bc ∷ b ∷ []) ⊢ (c ∷ [])
    bc⊢c = ImpL
      (Ax {A = B} {α = s})
      (Ax {A = C} {α = s})

    pab⊢c : (p ∷ a ∷ b ∷ []) ⊢ (c ∷ [])
    pab⊢c = ImpL
      (Ax {A = A} {α = s})
      bc⊢c

    pba⊢c : (p ∷ b ∷ a ∷ []) ⊢ (c ∷ [])
    pba⊢c = ExchangeL {Γ₁ = p ∷ []} {Γ₂ = []} pab⊢c

    bpa⊢c : (b ∷ p ∷ a ∷ []) ⊢ (c ∷ [])
    bpa⊢c = ExchangeL {Γ₁ = []} {Γ₂ = a ∷ []} pba⊢c

    qapa⊢c : (q ∷ a ∷ p ∷ a ∷ []) ⊢ (c ∷ [])
    qapa⊢c = ImpL
      (Ax {A = A} {α = s})
      bpa⊢c

    aqpa⊢c : (a ∷ q ∷ p ∷ a ∷ []) ⊢ (c ∷ [])
    aqpa⊢c = ExchangeL {Γ₁ = []} {Γ₂ = p ∷ a ∷ []} qapa⊢c

    apqa⊢c : (a ∷ p ∷ q ∷ a ∷ []) ⊢ (c ∷ [])
    apqa⊢c = ExchangeL {Γ₁ = a ∷ []} {Γ₂ = a ∷ []} aqpa⊢c

    apaq⊢c : (a ∷ p ∷ a ∷ q ∷ []) ⊢ (c ∷ [])
    apaq⊢c = ExchangeL {Γ₁ = a ∷ p ∷ []} {Γ₂ = []} apqa⊢c

    aaqq⊢c : (a ∷ a ∷ p ∷ q ∷ []) ⊢ (c ∷ [])
    aaqq⊢c = ExchangeL {Γ₁ = a ∷ []} {Γ₂ = q ∷ []} apaq⊢c

    apq⊢c : (a ∷ p ∷ q ∷ []) ⊢ (c ∷ [])
    apq⊢c = ContractL aaqq⊢c

    aqp⊢c : (a ∷ q ∷ p ∷ []) ⊢ (c ∷ [])
    aqp⊢c = ExchangeL {Γ₁ = a ∷ []} {Γ₂ = []} apq⊢c

    qp⊢a⇒c : (q ∷ p ∷ []) ⊢ (((A ⇒ C) ^ s) ∷ [])
    qp⊢a⇒c = ImpR aqp⊢c

    p⊢q⇒a⇒c : (p ∷ []) ⊢ (((A ⇒ B) ⇒ (A ⇒ C) ^ s) ∷ [])
    p⊢q⇒a⇒c = ImpR qp⊢a⇒c
  in
  ImpR p⊢q⇒a⇒c

derive-P3 : ∀ {A B : Formula} {s : Position}
  → [] ⊢ [ (((Not B) ⇒ (Not A)) ⇒ (((Not B) ⇒ A) ⇒ B)) ^ s ]
derive-P3 {A} {B} {s} =
  let
    p : PFormula
    p = ((Not B) ⇒ (Not A)) ^ s

    q : PFormula
    q = ((Not B) ⇒ A) ^ s

    a : PFormula
    a = A ^ s

    b : PFormula
    b = B ^ s

    ¬a : PFormula
    ¬a = (Not A) ^ s

    ¬b : PFormula
    ¬b = (Not B) ^ s

    emB : [] ⊢ (¬b ∷ b ∷ [])
    emB = NotR (Ax {A = B} {α = s})

    ¬a-a⊢b : (¬a ∷ a ∷ []) ⊢ (b ∷ [])
    ¬a-a⊢b =
      NotL
        (ExchangeR {Δ₁ = []} {Δ₂ = []}
          (WeakenR {A = B} {α = s}
            (Ax {A = A} {α = s})))

    pa⊢bb : (p ∷ a ∷ []) ⊢ (b ∷ b ∷ [])
    pa⊢bb = ImpL emB ¬a-a⊢b

    pa⊢b : (p ∷ a ∷ []) ⊢ (b ∷ [])
    pa⊢b = ContractR pa⊢bb

    ap⊢b : (a ∷ p ∷ []) ⊢ (b ∷ [])
    ap⊢b = ExchangeL {Γ₁ = []} {Γ₂ = []} pa⊢b

    qp⊢bb : (q ∷ p ∷ []) ⊢ (b ∷ b ∷ [])
    qp⊢bb = ImpL emB ap⊢b

    pq⊢bb : (p ∷ q ∷ []) ⊢ (b ∷ b ∷ [])
    pq⊢bb = ExchangeL {Γ₁ = []} {Γ₂ = []} qp⊢bb

    pq⊢b : (p ∷ q ∷ []) ⊢ (b ∷ [])
    pq⊢b = ContractR pq⊢bb

    qp⊢b : (q ∷ p ∷ []) ⊢ (b ∷ [])
    qp⊢b = ExchangeL {Γ₁ = []} {Γ₂ = []} pq⊢b

    p⊢q⇒b : (p ∷ []) ⊢ ((((Not B) ⇒ A) ⇒ B ^ s) ∷ [])
    p⊢q⇒b = ImpR qp⊢b
  in
  ImpR p⊢q⇒b

derive-K : ∀ {A B : Formula} {s : Position}
  → [] ⊢ [ (□ (A ⇒ B) ⇒ (□ A ⇒ □ B)) ^ s ]
derive-K {A} {B} {s} =
  let
    t : Position
    t = s ++ [ zero ]

    a : PFormula
    a = A ^ t

    b : PFormula
    b = B ^ t

    imp : PFormula
    imp = (A ⇒ B) ^ t

    boxImp : PFormula
    boxImp = □ (A ⇒ B) ^ s

    boxA : PFormula
    boxA = □ A ^ s

    impA⊢b : (imp ∷ a ∷ []) ⊢ (b ∷ [])
    impA⊢b = ImpL
      (Ax {A = A} {α = t})
      (Ax {A = B} {α = t})

    aImp⊢b : (a ∷ imp ∷ []) ⊢ (b ∷ [])
    aImp⊢b = ExchangeL {Γ₁ = []} {Γ₂ = []} impA⊢b

    c1 : modalConstraint M s t (a ∷ []) (b ∷ [])
    c1 = modalConstraint-step (has-head {F = A} {s = t} {Γ = b ∷ []})

    aBoxImp⊢b : (a ∷ boxImp ∷ []) ⊢ (b ∷ [])
    aBoxImp⊢b = BoxL c1 aImp⊢b

    boxImpA⊢b : (boxImp ∷ a ∷ []) ⊢ (b ∷ [])
    boxImpA⊢b = ExchangeL {Γ₁ = []} {Γ₂ = []} aBoxImp⊢b

    c2 : modalConstraint M s t (boxImp ∷ []) (b ∷ [])
    c2 = modalConstraint-step
      (has-append-right-singleton {Γ = boxImp ∷ []} {F = B} {s = t})

    boxImpBoxA⊢b : (boxImp ∷ boxA ∷ []) ⊢ (b ∷ [])
    boxImpBoxA⊢b = BoxL c2 boxImpA⊢b

    fr : t ∉Init (boxImp ∷ boxA ∷ [])
    fr = ∉Init-++ [ boxImp ] [ boxA ] step∉Init-single step∉Init-single

    boxImpBoxA⊢boxB : (boxImp ∷ boxA ∷ []) ⊢ ((□ B ^ s) ∷ [])
    boxImpBoxA⊢boxB = BoxR fr boxImpBoxA⊢b

    boxABoxImp⊢boxB : (boxA ∷ boxImp ∷ []) ⊢ ((□ B ^ s) ∷ [])
    boxABoxImp⊢boxB = ExchangeL {Γ₁ = []} {Γ₂ = []} boxImpBoxA⊢boxB

    boxImp⊢boxA⇒boxB : (boxImp ∷ []) ⊢ (((□ A ⇒ □ B) ^ s) ∷ [])
    boxImp⊢boxA⇒boxB = ImpR boxABoxImp⊢boxB
  in
  ImpR boxImp⊢boxA⇒boxB

derive-Dual1 : ∀ {A : Formula} {s : Position}
  → [] ⊢ [ (♢ A ⇒ Not (□ (Not A))) ^ s ]
derive-Dual1 {A} {s} =
  let
    t : Position
    t = s ++ [ zero ]

    a : PFormula
    a = A ^ t

    ¬a : PFormula
    ¬a = Not A ^ t

    box¬a : PFormula
    box¬a = □ (Not A) ^ s

    p0 : (¬a ∷ a ∷ []) ⊢ []
    p0 = NotL (Ax {A = A} {α = t})

    p1 : (a ∷ ¬a ∷ []) ⊢ []
    p1 = ExchangeL {Γ₁ = []} {Γ₂ = []} p0

    c : modalConstraint M s t (a ∷ []) []
    c = modalConstraint-step (has-singleton {F = A} {s = t})

    p2 : (a ∷ box¬a ∷ []) ⊢ []
    p2 = BoxL c p1

    p3 : (box¬a ∷ a ∷ []) ⊢ []
    p3 = ExchangeL {Γ₁ = []} {Γ₂ = []} p2

    fr : t ∉Init (box¬a ∷ [])
    fr = step∉Init-single

    p4 : (box¬a ∷ (♢ A ^ s) ∷ []) ⊢ []
    p4 = DiaL fr p3

    p5 : ((♢ A ^ s) ∷ []) ⊢ ((Not (□ (Not A)) ^ s) ∷ [])
    p5 = NotR p4
  in
  ImpR p5

derive-Dual2 : ∀ {A : Formula} {s : Position}
  → [] ⊢ [ (Not (□ (Not A)) ⇒ ♢ A) ^ s ]
derive-Dual2 {A} {s} =
  let
    t : Position
    t = s ++ [ zero ]

    ¬a : PFormula
    ¬a = Not A ^ t

    p0 : [] ⊢ (¬a ∷ (A ^ t) ∷ [])
    p0 = NotR (Ax {A = A} {α = t})

    p1 : [] ⊢ ((A ^ t) ∷ ¬a ∷ [])
    p1 = ExchangeR {Δ₁ = []} {Δ₂ = []} p0

    c : modalConstraint M s t [] (¬a ∷ [])
    c = modalConstraint-step (has-singleton {F = Not A} {s = t})

    p2 : [] ⊢ ((♢ A ^ s) ∷ ¬a ∷ [])
    p2 = DiaR c p1

    p3 : [] ⊢ (¬a ∷ (♢ A ^ s) ∷ [])
    p3 = ExchangeR {Δ₁ = []} {Δ₂ = []} p2

    fr : t ∉Init ((♢ A ^ s) ∷ [])
    fr = step∉Init-single

    p4 : [] ⊢ ((□ (Not A) ^ s) ∷ (♢ A ^ s) ∷ [])
    p4 = BoxR fr p3

    p6 : ((Not (□ (Not A)) ^ s) ∷ []) ⊢ ((♢ A ^ s) ∷ [])
    p6 = NotL p4
  in
  ImpR p6

d-step-gen : (m : Logic) → HasD m
  → ∀ {s : Position} {u : Token} {Γ Δ : Ctx}
  → modalConstraint m s (s ++ [ u ]) Γ Δ
d-step-gen D tt {u = u} = u , refl
d-step-gen D4 tt = strict-step

d-step : HasD M
  → ∀ {s : Position} {u : Token} {Γ Δ : Ctx}
  → modalConstraint M s (s ++ [ u ]) Γ Δ
d-step = d-step-gen M

t-self-gen : (m : Logic) → HasT m
  → ∀ {s : Position} {Γ Δ : Ctx}
  → modalConstraint m s s Γ Δ
t-self-gen T tt = inl refl
t-self-gen S4 tt = ⊑-refl _
t-self-gen S4dot2 tt = subset-refl
t-self-gen S5 tt = tt

t-self : HasT M
  → ∀ {s : Position} {Γ Δ : Ctx}
  → modalConstraint M s s Γ Δ
t-self = t-self-gen M

step2-has4-gen : (m : Logic) → Has4 m
  → ∀ {A : Formula} {s : Position}
  → modalConstraint m s ((s ++ [ zero ]) ++ [ suc zero ]) [] ((A ^ ((s ++ [ zero ]) ++ [ suc zero ])) ∷ [])
step2-has4-gen K4 tt = strict-step-step , has-singleton
step2-has4-gen D4 tt = strict-step-step
step2-has4-gen S4 tt = prefix-step-step
step2-has4-gen S4dot2 tt = subset-step-step

step2-has4 : Has4 M
  → ∀ {A : Formula} {s : Position}
  → modalConstraint M s ((s ++ [ zero ]) ++ [ suc zero ]) [] ((A ^ ((s ++ [ zero ]) ++ [ suc zero ])) ∷ [])
step2-has4 = step2-has4-gen M

modal-has5-gen : (m : Logic) → Has5 m
  → ∀ {α β : Position} {Γ Δ : Ctx}
  → modalConstraint m α β Γ Δ
modal-has5-gen S5 tt = tt

modal-has5 : Has5 M
  → ∀ {α β : Position} {Γ Δ : Ctx}
  → modalConstraint M α β Γ Δ
modal-has5 = modal-has5-gen M

modal-C-dia-gen : (m : Logic) → HasC m
  → ∀ {A : Formula} {s : Position}
  → modalConstraint m (s ++ [ suc zero ]) ((s ++ [ zero ]) ++ [ suc zero ]) ((A ^ ((s ++ [ zero ]) ++ [ suc zero ])) ∷ []) []
modal-C-dia-gen S4dot2 tt {s = s} = subset-step1-into-step0-1 {xs = s}

modal-C-dia : HasC M
  → ∀ {A : Formula} {s : Position}
  → modalConstraint M (s ++ [ suc zero ]) ((s ++ [ zero ]) ++ [ suc zero ]) ((A ^ ((s ++ [ zero ]) ++ [ suc zero ])) ∷ []) []
modal-C-dia = modal-C-dia-gen M

modal-C-box-gen : (m : Logic) → HasC m
  → ∀ {A : Formula} {s : Position}
  → modalConstraint m (s ++ [ zero ]) ((s ++ [ zero ]) ++ [ suc zero ]) [] ((♢ A ^ (s ++ [ suc zero ])) ∷ [])
modal-C-box-gen S4dot2 tt = subset-step-right

modal-C-box : HasC M
  → ∀ {A : Formula} {s : Position}
  → modalConstraint M (s ++ [ zero ]) ((s ++ [ zero ]) ++ [ suc zero ]) [] ((♢ A ^ (s ++ [ suc zero ])) ∷ [])
modal-C-box = modal-C-box-gen M

derive-D : HasD M → ∀ {A : Formula} {s : Position}
  → [] ⊢ [ (□ A ⇒ ♢ A) ^ s ]
derive-D h {A} {s} =
  let
    t : Position
    t = s ++ [ zero ]

    p0 : ((A ^ t) ∷ []) ⊢ ((A ^ t) ∷ [])
    p0 = Ax {A = A} {α = t}

    p1 : ((□ A ^ s) ∷ []) ⊢ ((A ^ t) ∷ [])
    p1 = BoxL (d-step h {s = s} {u = zero} {Γ = []} {Δ = (A ^ t) ∷ []}) p0

    p2 : ((□ A ^ s) ∷ []) ⊢ ((♢ A ^ s) ∷ [])
    p2 = DiaR (d-step h {s = s} {u = zero} {Γ = (□ A ^ s) ∷ []} {Δ = []}) p1
  in
  ImpR p2

derive-T : HasT M → ∀ {A : Formula} {s : Position}
  → [] ⊢ [ (□ A ⇒ A) ^ s ]
derive-T h {A} {s} =
  ImpR (BoxL (t-self h {s = s} {Γ = []} {Δ = (A ^ s) ∷ []}) (Ax {A = A} {α = s}))

derive-4 : Has4 M → ∀ {A : Formula} {s : Position}
  → [] ⊢ [ (□ A ⇒ □ (□ A)) ^ s ]
derive-4 h {A} {s} =
  let
    t0 : Position
    t0 = s ++ [ zero ]

    t1 : Position
    t1 = t0 ++ [ suc zero ]

    p0 : ((□ A ^ s) ∷ []) ⊢ ((A ^ t1) ∷ [])
    p0 = BoxL (step2-has4 h {A = A} {s = s}) (Ax {A = A} {α = t1})

    fr1 : t1 ∉Init ((□ A ^ s) ∷ [])
    fr1 = stepStep∉Init-single {F = □ A} {s = s} {u = zero} {v = suc zero}

    p1 : ((□ A ^ s) ∷ []) ⊢ ((□ A ^ t0) ∷ [])
    p1 = BoxR {α = t0} {x = suc zero} fr1 p0

    fr0 : t0 ∉Init ((□ A ^ s) ∷ [])
    fr0 = step∉Init-single {F = □ A} {s = s} {u = zero}

    p2 : ((□ A ^ s) ∷ []) ⊢ ((□ (□ A) ^ s) ∷ [])
    p2 = BoxR {α = s} {x = zero} fr0 p1
  in
  ImpR p2

derive-5 : Has5 M → ∀ {A : Formula} {s : Position}
  → [] ⊢ [ (♢ A ⇒ □ (♢ A)) ^ s ]
derive-5 h {A} {s} =
  let
    t0 : Position
    t0 = s ++ [ zero ]

    t1 : Position
    t1 = s ++ [ suc zero ]

    p0 : ((A ^ t1) ∷ []) ⊢ ((A ^ t1) ∷ [])
    p0 = Ax {A = A} {α = t1}

    p1 : ((A ^ t1) ∷ []) ⊢ ((♢ A ^ t0) ∷ [])
    p1 = DiaR (modal-has5 h {α = t0} {β = t1} {Γ = (A ^ t1) ∷ []} {Δ = []}) p0

    fr0 : t0 ∉Init ((A ^ t1) ∷ [])
    fr0 = stepDiff∉Init-single {F = A} {s = s} {u = zero} {v = suc zero} 0≢1

    p2 : ((A ^ t1) ∷ []) ⊢ ((□ (♢ A) ^ s) ∷ [])
    p2 = BoxR {α = s} {x = zero} fr0 p1

    fr1 : t1 ∉Init ((□ (♢ A) ^ s) ∷ [])
    fr1 = step∉Init-single {F = □ (♢ A)} {s = s} {u = suc zero}

    p3 : ((♢ A ^ s) ∷ []) ⊢ ((□ (♢ A) ^ s) ∷ [])
    p3 = DiaL
      {Γ = []} {Δ = (□ (♢ A) ^ s) ∷ []}
      {A = A} {α = s} {x = suc zero}
      fr1 p2
  in
  ImpR p3

derive-C : HasC M → ∀ {A : Formula} {s : Position}
  → [] ⊢ [ (♢ (□ A) ⇒ □ (♢ A)) ^ s ]
derive-C h {A} {s} =
  let
    t0 : Position
    t0 = s ++ [ zero ]

    t1 : Position
    t1 = s ++ [ suc zero ]

    u : Position
    u = t0 ++ [ suc zero ]

    p0 : ((A ^ u) ∷ []) ⊢ ((A ^ u) ∷ [])
    p0 = Ax {A = A} {α = u}

    p1 : ((A ^ u) ∷ []) ⊢ ((♢ A ^ t1) ∷ [])
    p1 = DiaR (modal-C-dia h {A = A} {s = s}) p0

    p2 : ((□ A ^ t0) ∷ []) ⊢ ((♢ A ^ t1) ∷ [])
    p2 = BoxL (modal-C-box h {A = A} {s = s}) p1

    fr0 : t1 ∉Init ((□ A ^ t0) ∷ [])
    fr0 = stepDiff∉Init-single {F = □ A} {s = s} {u = suc zero} {v = zero} 1≢0

    p3 : ((□ A ^ t0) ∷ []) ⊢ ((□ (♢ A) ^ s) ∷ [])
    p3 = BoxR {α = s} {x = suc zero} fr0 p2

    fr1 : t0 ∉Init ((□ (♢ A) ^ s) ∷ [])
    fr1 = step∉Init-single {F = □ (♢ A)} {s = s} {u = zero}

    p4 : ((♢ (□ A) ^ s) ∷ []) ⊢ ((□ (♢ A) ^ s) ∷ [])
    p4 = DiaL
      {Γ = []} {Δ = (□ (♢ A) ^ s) ∷ []}
      {A = □ A} {α = s} {x = zero}
      fr1 p3
  in
  ImpR p4

------------------------------------------------------------------------
-- Main theorem at arbitrary position

completeAt : ∀ (s : Position) {A : Formula}
  → M ⊢ₕ A
  → [] ⊢ [ A ^ s ]
completeAt s (ax P1) = derive-P1 {s = s}
completeAt s (ax P2) = derive-P2 {s = s}
completeAt s (ax P3) = derive-P3 {s = s}
completeAt s (ax AxK) = derive-K {s = s}
completeAt s (ax AxDual1) = derive-Dual1 {s = s}
completeAt s (ax AxDual2) = derive-Dual2 {s = s}
completeAt s (ax (AxD h)) = derive-D h {s = s}
completeAt s (ax (AxT h)) = derive-T h {s = s}
completeAt s (ax (Ax4 h)) = derive-4 h {s = s}
completeAt s (ax (Ax5 h)) = derive-5 h {s = s}
completeAt s (ax (AxC h)) = derive-C h {s = s}
completeAt s (MP {A = A} {B = B} p q) =
  Cut {A = A ⇒ B} {α = s}
    cutWitness-MP
    (completeAt s q)
    (ImpL (completeAt s p) (Ax {A = B} {α = s}))
completeAt s (NEC p) =
  BoxR {α = s} {x = zero}
    step∉Init[]
    (completeAt (s ++ [ zero ]) p)

-- %<*hilbertComplete>
completeness : ∀ {A : Formula}
  → M ⊢ₕ A
  → [] ⊢ [ A ^ [] ]
completeness = completeAt []
-- %</hilbertComplete>
