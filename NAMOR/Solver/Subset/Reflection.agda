{-# OPTIONS --safe #-}

module NAMOR.Solver.Subset.Reflection where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; false; true; if_then_else_)
open import Cubical.Data.List using (List; []; _∷_; _++_; [_])
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit)

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String

open import Cubical.Reflection.Base
open import Cubical.Tactics.Reflection using (wait-for-type)
open import Cubical.Tactics.Reflection.Variables

open import NAMOR.List.Membership as Mem using (_∈_)
open import NAMOR.Solver.Subset as Sub

private
  _==_ : Name → Name → Bool
  _==_ = primQNameEquality
  {-# INLINE _==_ #-}

  record BuildState : Type where
    constructor mkState
    field
      listVars : Vars
      elemVars : Vars

  ExprTemplate : Type
  ExprTemplate = VarAss → VarAss → Term

  emptyState : BuildState
  emptyState = mkState [] []

  mergeState : BuildState → BuildState → BuildState
  mergeState s₁ s₂ =
    mkState
      (appendWithoutRepetition (BuildState.listVars s₁) (BuildState.listVars s₂))
      (appendWithoutRepetition (BuildState.elemVars s₁) (BuildState.elemVars s₂))

  addListVar : Term → BuildState
  addListVar t = mkState (addWithoutRepetition t []) []

  addElemVar : Term → BuildState
  addElemVar t = mkState [] (addWithoutRepetition t [])

  natTerm : Maybe ℕ → Term
  natTerm (just n) = lit (nat n)
  natTerm nothing = unknown

  mkListTerm : List Term → Term
  mkListTerm [] = con (quote []) []
  mkListTerm (t ∷ ts) = con (quote _∷_) (varg t ∷ varg (mkListTerm ts) ∷ [])

  hargω : Term → Arg Term
  hargω t = arg (arg-info hidden (modality relevant quantity-ω)) t

  visibleArgs : List (Arg Term) → List Term
  visibleArgs [] = []
  visibleArgs (arg (arg-info visible m) t ∷ args) = t ∷ visibleArgs args
  visibleArgs (_ ∷ args) = visibleArgs args

  parseMembershipArgs : List Term → Maybe (Term × Term)
  parseMembershipArgs (x ∷ xs ∷ []) = just (x , xs)
  parseMembershipArgs _ = nothing

  parseSingletonArg : List Term → Maybe Term
  parseSingletonArg (x ∷ []) = just x
  parseSingletonArg _ = nothing

  dropIndex : ℕ → ℕ → Maybe ℕ
  dropIndex zero i = just i
  dropIndex (suc k) zero = nothing
  dropIndex (suc k) (suc i) = dropIndex k i

  lowerArgs : ℕ → List (Arg Term) → Maybe (List (Arg Term))
  lowerAbs : ℕ → Abs Term → Maybe (Abs Term)
  lowerTerm : ℕ → Term → Maybe Term

  lowerArgs k [] = just []
  lowerArgs k (arg i t ∷ args) with lowerTerm k t | lowerArgs k args
  ... | just t' | just args' = just (arg i t' ∷ args')
  ... | _ | _ = nothing

  lowerAbs k (abs s t) with lowerTerm (suc k) t
  ... | just t' = just (abs s t')
  ... | nothing = nothing

  lowerTerm k (var i args) with dropIndex k i | lowerArgs k args
  ... | just i' | just args' = just (var i' args')
  ... | _ | _ = nothing
  lowerTerm k (con c args) with lowerArgs k args
  ... | just args' = just (con c args')
  ... | nothing = nothing
  lowerTerm k (def f args) with lowerArgs k args
  ... | just args' = just (def f args')
  ... | nothing = nothing
  lowerTerm k (meta m args) with lowerArgs k args
  ... | just args' = just (meta m args')
  ... | nothing = nothing
  lowerTerm k (lam v b) with lowerAbs k b
  ... | just b' = just (lam v b')
  ... | nothing = nothing
  lowerTerm k (pi (arg i a) b) with lowerTerm k a | lowerAbs k b
  ... | just a' | just b' = just (pi (arg i a') b')
  ... | _ | _ = nothing
  lowerTerm k (pat-lam cs args) with lowerArgs k args
  ... | just args' = just (pat-lam cs args')
  ... | nothing = nothing
  lowerTerm k (agda-sort s) = just (agda-sort s)
  lowerTerm k (lit l) = just (lit l)
  lowerTerm k unknown = just unknown

  resolveName : Term → Maybe Name
  resolveName (def n _) = just n
  resolveName (lit (name n)) = just n
  resolveName _ = nothing

  asNameTerm : Term → Term
  asNameTerm (lit (name n)) = def n []
  asNameTerm t = t

  listVarTemplate : Term → ExprTemplate × BuildState
  listVarTemplate t =
    ( (λ assL assE →
          con (quote Sub.SubsetSolver.var)
            (varg (natTerm (assL t)) ∷ []))
    , addListVar t
    )

  elemTemplate : Term → ExprTemplate × BuildState
  elemTemplate t =
    ( (λ assL assE →
          con (quote Sub.SubsetSolver.elm)
            (varg (natTerm (assE t)) ∷ []))
    , addElemVar t
    )

  appendTemplates : (ExprTemplate × BuildState) → (ExprTemplate × BuildState)
                 → (ExprTemplate × BuildState)
  appendTemplates (e₁ , s₁) (e₂ , s₂) =
    ( (λ assL assE →
          con (quote Sub.SubsetSolver._++ₑ_)
            (varg (e₁ assL assE) ∷ varg (e₂ assL assE) ∷ []))
    , mergeState s₁ s₂
    )

  nilTemplate : ExprTemplate × BuildState
  nilTemplate = ((λ _ _ → con (quote Sub.SubsetSolver.[]ₑ) []) , emptyState)

  remTemplate : (ExprTemplate × BuildState) → Term → (ExprTemplate × BuildState)
  remTemplate (e , s) x =
    ( (λ assL assE →
          con (quote Sub.SubsetSolver.rem)
            (varg (e assL assE) ∷ varg (natTerm (assE x)) ∷ []))
    , mergeState s (addElemVar x)
    )

  mutual
    argsSize : List (Arg Term) → ℕ
    argsSize [] = zero
    argsSize (arg i t ∷ args) = termSize t + argsSize args

    absSize : Abs Term → ℕ
    absSize (abs _ t) = termSize t

    termSize : Term → ℕ
    termSize (var _ args) = suc (argsSize args)
    termSize (con _ args) = suc (argsSize args)
    termSize (def _ args) = suc (argsSize args)
    termSize (meta _ args) = suc (argsSize args)
    termSize (lam _ b) = suc (absSize b)
    termSize (pi (arg _ a) b) = suc (termSize a + absSize b)
    termSize (pat-lam _ args) = suc (argsSize args)
    termSize (agda-sort _) = suc zero
    termSize (lit _) = suc zero
    termSize unknown = suc zero

  maybeTC : ∀ {A B : Type} → Maybe A → (A → TC B) → TC B → TC B
  maybeTC (just x) f fallback = f x
  maybeTC nothing f fallback = fallback

  canonicalize : Term → TC Term
  canonicalize t = withNormalisation true (reduce t)

  mkListVarExpr : Term → TC (ExprTemplate × BuildState)
  mkListVarExpr t =
    do
      t' ← canonicalize t
      returnTC (listVarTemplate t')

  mkElemExpr : Term → TC (ExprTemplate × BuildState)
  mkElemExpr t =
    do
      t' ← canonicalize t
      returnTC (elemTemplate t')

  buildExpressionFuel : Name → ℕ → Term → TC (ExprTemplate × BuildState)
  buildExpressionFuel removeName zero t = mkListVarExpr t
  buildExpressionFuel removeName (suc fuel) (con c args) =
    if c == (quote [])
    then returnTC ((λ _ _ → con (quote Sub.SubsetSolver.[]ₑ) []) , emptyState)
    else if c == (quote _∷_)
         then maybeTC (parseMembershipArgs (visibleArgs args))
                (λ where
                  (x , xs) →
                    do
                      x' ← mkElemExpr x
                      rhs ← buildExpressionFuel removeName fuel xs
                      returnTC (appendTemplates x' rhs))
                (mkListVarExpr (con c args))
         else mkListVarExpr (con c args)

  buildExpressionFuel removeName (suc fuel) (def f args) =
    if f == (quote [_])
    then maybeTC (parseSingletonArg (visibleArgs args))
           (λ x →
             do
               x' ← mkElemExpr x
               returnTC (appendTemplates x' nilTemplate))
           (mkListVarExpr (def f args))
    else if f == (quote _++_)
    then maybeTC (parseMembershipArgs (visibleArgs args))
           (λ where
             (l , r) →
               do
                 l' ← buildExpressionFuel removeName fuel l
                 r' ← buildExpressionFuel removeName fuel r
                 returnTC (appendTemplates l' r'))
           (mkListVarExpr (def f args))
    else if f == removeName
         then maybeTC (parseMembershipArgs (visibleArgs args))
                (λ where
                  (xs , x) →
                    do
                      xs' ← buildExpressionFuel removeName fuel xs
                      x' ← canonicalize x
                      returnTC (remTemplate xs' x'))
                (mkListVarExpr (def f args))
         else do
           unfolded ← reduce (def f args)
           buildExpressionFuel removeName fuel unfolded

  buildExpressionFuel removeName (suc fuel) t = mkListVarExpr t

  buildExpression : Name → Term → TC (ExprTemplate × BuildState)
  buildExpression removeName t = buildExpressionFuel removeName (termSize t) t

  extractMembershipSides : Term → Maybe (Term × Term)
  extractMembershipSides (def f args) =
    if f == (quote Mem._∈_)
    then parseMembershipArgs (visibleArgs args)
    else nothing
  extractMembershipSides _ = nothing

  lowerGoalSides : ℕ → Term → Term → TC (Term × Term)
  lowerGoalSides k lhs rhs with lowerTerm k lhs | lowerTerm (suc k) rhs
  ... | just lhs' | just rhs' = returnTC (lhs' , rhs')
  ... | _ | _ =
    typeError
      (strErr "solve⊆!: goal lists must not depend on subset binder variables." ∷ [])

  extractGoalSidesAt : ℕ → Term → TC (Term × Term)
  extractGoalSidesAt k (pi (arg _ dom) (abs _ cod)) with extractMembershipSides dom | extractMembershipSides cod
  ... | just (_ , lhs) | just (_ , rhs) = lowerGoalSides k lhs rhs
  ... | just _ | nothing =
    typeError
      (strErr "solve⊆!: expected membership in codomain, got " ∷ termErr cod ∷ [])
  ... | nothing | _ = extractGoalSidesAt (suc k) cod
  extractGoalSidesAt k goal =
    typeError
      (strErr "solve⊆!: expected goal of shape (x ∈ lhs) → x ∈ rhs, got " ∷ termErr goal ∷ [])

  extractGoalSides : Term → TC (Term × Term)
  extractGoalSides = extractGoalSidesAt 0

  solverCall : Term → Term → Term → Term → Term
  solverCall discrete e₁ e₂ env =
    def (quote Sub.Solver.solve)
      (varg discrete ∷ varg e₁ ∷ varg e₂ ∷ varg env ∷ hargω (def (quote refl) []) ∷ [])

  requireName : Term → TC Name
  requireName removeOp with resolveName removeOp
  ... | just n = returnTC n
  ... | nothing =
    typeError
      (strErr "solve⊆!: first argument must be an operator name or quote name, got "
        ∷ termErr removeOp ∷ [])

  solve⊆!-macro : Term → Term → Term → TC Unit
  solve⊆!-macro removeOp discrete hole =
    do
      removeName ← requireName removeOp

      let discrete' = asNameTerm discrete

      goal ← withNormalisation false (
                withReduceDefs (false , quote Mem._∈_ ∷ quote _++_ ∷ removeName ∷ [])
                  (inferType hole >>= reduce))
      goal' ← wait-for-type goal
      (lhs , rhs) ← extractGoalSides goal'

      lhsBuilt ← buildExpression removeName lhs
      rhsBuilt ← buildExpression removeName rhs

      let st = mergeState (snd lhsBuilt) (snd rhsBuilt)
      let lvars = BuildState.listVars st
      let evars = BuildState.elemVars st

      let assL : VarAss
          assL t = indexOf t lvars

      let assE : VarAss
          assE t = indexOf t evars

      let lhsExpr = fst lhsBuilt assL assE
      let rhsExpr = fst rhsBuilt assL assE
      let env = con (quote _,_) (varg (mkListTerm lvars) ∷ varg (mkListTerm evars) ∷ [])

      unify hole (solverCall discrete' lhsExpr rhsExpr env)

solve⊆-tc : Term → Term → Term → TC Unit
solve⊆-tc = solve⊆!-macro

macro
  solve⊆! : Term → Term → Term → TC _
  solve⊆! = solve⊆!-macro
