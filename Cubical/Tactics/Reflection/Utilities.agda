{-

This module provides utilities for traversing the reflected representation of terms using monadic operations. It is designed to apply operations specifically at `variable`, `constructor`, and `definition` nodes. It also handles the lifting of terms inside lambda expressions and pattern lambdas.

### General Overview

- **Functionality**:
  - Assists in traversing reflected terms.
  - Applies operations at specific nodes (`variable`, `constructor`, `definition`).
  - Manages lifting within lambda and pattern lambda expressions.

- **Usages**:
  - Can act either as a fold or a map depending on the application with diferent monads.
  - Facilitates easier refactoring of code when the reflected representation changes.
  - Handles termination issues that are cumbersome when functions traverse or map over reflected terms.
  - Allows for the easy inclusion of state or error handling while refactoring functions operating over terms.

#### Specialized Transformations

- **`remapVars`**:
  - Remaps variables using a specified function.

- **`replaceVarWithCon`**:
  - Replaces variables with constructors based on a mapping function.

- **`liftVars`** and **`liftVarsFrom`**:
  - Functions to lift variables by a specified amount.

- **`dropVar`**:
  - Drops a specified variable.

#### Modules for Specific Transformations

- **`LiftFrom`**:
  - Provides a public interface for lifting variables by a specified amount.

- **`dropVars`**:
  - Offers a function to drop a specified number of variables.

#### Additional Utilities

- **`invVar`**:
  - Replaces Interval variable with a negated form.

- **`hasVar`** and **`hasVarBy`**:
  - Checks for the presence of a variable based on given conditions.

- **`findInterval`**:
  - Finds an interval within a term.

- **`replaceVarWithTerm`**:
  - Replaces variables with terms based on a mapping function.

- **`substTms`**:
  - Substitutes a list of terms into a given term.

- **`replaceAtTrm`**:
  - Replaces a term at a specified variable position.

-}

{-# OPTIONS --safe #-}
module Cubical.Tactics.Reflection.Utilities where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_ ; _<_ to _<ℕ_)

open import Cubical.Reflection.Base
open import Cubical.Reflection.Sugar
open import Cubical.Data.List as L
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.FinData using () renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; suc; _+_; zero; _∸_; discreteℕ; predℕ)

open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables


finiteNumberAsTerm : Maybe ℕ → Term
finiteNumberAsTerm (just ℕ.zero) = con (quote fzero) []
finiteNumberAsTerm (just (ℕ.suc n)) = con (quote fsuc) (finiteNumberAsTerm (just n) v∷ [])
finiteNumberAsTerm _ = unknown

-- error message helper
errorOut : List (Arg Term) → TC (Template × Vars)
errorOut something = typeError (strErr "Don't know what to do with " ∷ map (λ {(arg _ t) → termErr t}) something)

errorOut' : Term → TC (Template × Vars)
errorOut' something = typeError (strErr "Don't know what to do with " ∷ termErr something ∷ [])


_==_ = primQNameEquality
{-# INLINE _==_ #-}

mapArg : ∀ {ℓ ℓ'} → {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B) → Arg A → Arg B
mapArg f (arg i x) = arg i (f x)

unArg : ∀ {ℓ} → {A : Type ℓ} → Arg A → A
unArg (arg i x) = x

argInfo : ∀ {ℓ} → {A : Type ℓ} → Arg A → ArgInfo
argInfo (arg i x) = i

module atVarOrConOrDefMmp {M : Functorω}
              {{RA : RawApplicative M}} {{_ : RawMonad M {{RA}} }}
              (f : ℕ → ℕ → (List (Arg Term)) → M (List (Arg Term)) → (List (M (Arg Term))) → (M Term))
              (h : ℕ → Name → (List (Arg Term)) → M (List (Arg Term)) → (List (M (Arg Term))) → (M Term))
              (g : ℕ → Name → (List (Arg Term)) → M (List (Arg Term)) → (List (M (Arg Term))) → (M Term))
              where

 ra : ℕ → List (Arg Term) → M (List (Arg Term))
 raT : ℕ → List (Arg Term) → (List (M (Arg Term)))
 rc : ℕ → List Clause → M (List Clause)
 rcl : ℕ → Clause → M Clause
 rtl : ℕ → Telescope → M Telescope
 rv : ℕ →  Term → M Term

 rpt : ℕ → Pattern → M Pattern
 rpts : ℕ → List (Arg Pattern) → M (List (Arg Pattern))
 rs : ℕ →  Sort → M Sort

 ra n [] = ⦇ [] ⦈
 ra n (arg i x ∷ x₂) =
   ⦇ ⦇ (arg i) (rv n x) ⦈ ∷ ra n x₂ ⦈

 raT n [] = []
 raT n (arg i x ∷ x₂) =
   ⦇ (arg i) (rv n x) ⦈ ∷ raT n x₂

 rv n (var x args) = f n x args (ra n args) (raT n args)
 rv n (con c args) = h n c args (ra n args) (raT n args)
 rv n (def f' args) = g n f' args (ra n args) (raT n args)
 rv n (lam v₁ (abs s x)) =
   (lam v₁) <$> (abs s <$> (rv (suc n) x))
 rv n (pat-lam cs args) = ⦇ pat-lam (rc n cs) (ra n args) ⦈
 rv n (pi (arg i x) (abs s x₁)) =
  ⦇ pi ((arg i) <$> rv n x) (abs s <$> rv (suc n) x₁) ⦈
 rv n (agda-sort s) = ⦇ agda-sort (rs n s) ⦈
 rv n (lit l) = ⦇ (lit l) ⦈
 rv n (meta x x₁) = ⦇ meta ⦇ x ⦈ (ra n x₁) ⦈
 rv n unknown = ⦇ unknown ⦈


 rs n (set t) = ⦇ set (rv n t) ⦈
 rs n (lit n₁) = ⦇ (lit n₁) ⦈
 rs n (prop t) = ⦇ prop (rv n t) ⦈
 rs n (propLit n₁) = ⦇ (propLit n₁) ⦈
 rs n (inf n₁) = ⦇ (inf n₁) ⦈
 rs n unknown = ⦇ unknown ⦈

 rtl n [] = ⦇ [] ⦈
 rtl n ((v , arg i x) ∷ xs) =
    ⦇ ⦇ ⦇ v ⦈ , ⦇ arg ⦇ i ⦈ (rv n x) ⦈ ⦈ ∷ rtl (suc n) xs ⦈

 rc n [] = ⦇ [] ⦈
 rc n (cl ∷ cls) =
   ⦇ rcl n cl ∷ rc n cls ⦈


 rcl n (clause tel ps t) =
   ⦇ clause (rtl n tel) (rpts n ps) (rv (length tel + n) t) ⦈
 rcl n (absurd-clause tel ps) =
   ⦇ absurd-clause (rtl n tel) (rpts n ps) ⦈



 rpt n (con c ps) = con c <$> (rpts n ps)
 rpt n (dot t) = dot <$> (rv n t)
 rpt n (var x) = pure $ var x
 rpt n (lit l) = pure $ lit l
 rpt n (proj f) = pure $ proj f
 rpt n (absurd x) = pure $ absurd x

 rpts n [] = ⦇ [] ⦈
 rpts n ((arg i x) ∷ xs) = ⦇ ⦇ arg ⦇ i ⦈ (rpt n x) ⦈ ∷ rpts n xs ⦈

 rv0 = rv 0

atVarOrConOrDefMmp = atVarOrConOrDefMmp.rv0


module atVarOrDefMmp {M : Functorω}
              {{RA : RawApplicative M}} {{RM : RawMonad M {{RA}} }}
              (f : ℕ → ℕ → (List (Arg Term)) → M (List (Arg Term)) → (List (M (Arg Term))) → (M Term))
              (g : ℕ → Name → (List (Arg Term)) → M (List (Arg Term)) → (List (M (Arg Term))) → (M Term))
              where
 open atVarOrConOrDefMmp {M} {{RA}} {{RM}}
         f
         (λ n c _ argsM _ → _<$>_ {M = M} (con c)  argsM)
         g public


atVarOrDefMmp = atVarOrDefMmp.rv0


module atVarOrDefM {M : Functorω}
              {{RA : RawApplicative M}} {{RM : RawMonad M {{RA}} }}
              (f : ℕ → ℕ → (List (Arg Term)) → M (List (Arg Term)) → (M Term))
              (g : ℕ → Name → (List (Arg Term)) → M (List (Arg Term)) → (M Term))
              where

 open atVarOrDefMmp {M = M}
              {{RA}} {{RM }}
              (λ n k l l' _ → f n k l l')
              (λ n k l l' _ → g n k l l') public

atVarOrDefM = atVarOrDefM.rv0

atVarOrM : (ℕ → ℕ → List (Arg Term) → Maybe Term) → (ℕ → Name → List (Arg Term) → Maybe Term) → Term → Term
atVarOrM f g = rv zero
 where
 open atVarOrDefM {{_}} {{RawMonadIdentityM}}
    (λ n k _ args →
          let t = var k args
              t' = (Mb.fromJust-def t (f n (k ∸ n) args))
          in (if (k <ℕ n) then t else t'))
   (λ n nm _ args →
          let t = def nm args
          in  Mb.fromJust-def t (g n nm args))

atVarOrM' : (ℕ → ℕ → List (Arg Term) → Maybe Term) → (ℕ → Name → List (Arg Term) → Maybe Term) → Term → Term
atVarOrM' f g = rv zero
 where
 open atVarOrDefM {{_}} {{RawMonadIdentityM}}
    (λ n k args0 args →
          let t = var k args
              t' = (Mb.fromJust-def t (f n (k ∸ n) args0))
          in (if (k <ℕ n) then t else t'))
   (λ n nm args0 args →
          Mb.fromJust-def (def nm args) (g n nm args0))

atVarOrConM' : (ℕ → ℕ → List (Arg Term) → Maybe Term) →
 (ℕ → Name → List (Arg Term) → Maybe Term)
 → (ℕ → Name → List (Arg Term) → Maybe Term) → Term → Term
atVarOrConM' f h g = rv zero
 where
 open atVarOrConOrDefMmp {{_}} {{RawMonadIdentityM}}
    (λ n k args0 args _ →
          let t = var k args
              t' = (Mb.fromJust-def t (f n (k ∸ n) args0))
          in (if (k <ℕ n) then t else t'))
   (λ n nm args0 args _ →
          Mb.fromJust-def (con nm args) (h n nm args0))
   (λ n nm args0 args _ →
          Mb.fromJust-def (def nm args) (g n nm args0))



module atVarM {M : Functorω}
              {{RA : RawApplicative M}} {{RM : RawMonad M {{RA}} }}
              (f : ℕ → ℕ → List (Arg Term) → Maybe (M Term)) where


 open atVarOrDefM
      (λ n k _ args → RawMonad._>>=_ RM args λ args →
          let t = var k args
          in (Mb.fromJust-def (RawApplicative.pure RA t) (if (k <ℕ n) then nothing else (f n (k ∸ n) args))))
      (λ n nm _ args → RawMonad._>>=_ RM args λ args → RawApplicative.pure RA (def nm args))
      public

module atVar (f : ℕ → ℕ → List (Arg Term) → Maybe (Term)) where

 open atVarM
      {{_}}
      {{RawMonadIdentityM}} f
      public

atVarM : {M : Functorω}
              {{RA : RawApplicative M}} {{_ : RawMonad M {{RA}} }}
              (f : ℕ → ℕ → List (Arg Term) → Maybe (M Term)) → Term → M Term
atVarM f = atVarM.rv f zero


atVar : (ℕ → ℕ → List (Arg Term) → Maybe Term) → Term → Term
atVar f = atVar.rv f zero

remapVars : (ℕ → ℕ) → Term → Term
remapVars f = atVar λ n k args → just (var (f k + n) args)


-- only for not applied vars!!
replaceVarWithCon : (ℕ → (Maybe Name)) → Term → Term
replaceVarWithCon f = atVar λ n k args → map-Maybe (λ nm → con nm []) (f k)

liftVars : Term → Term
liftVars = atVar λ n k args → just (var (n + suc k) args)

liftVarsFrom : ℕ → ℕ → Term → Term
liftVarsFrom m = atVar.rv (λ n k args → just (var (n + m + k) args))


module LiftFrom (m : ℕ) where
 open atVar (λ n k args → just (var (n + m + k) args)) public



dropVar : ℕ → Term → Term
dropVar = atVar.rv (λ n k args → just (var (n + predℕ k) args))



module dropVars (m : ℕ) where
 open atVar (λ n k args → just (var (n + (k ∸ m)) args)) public



invVar : ℕ → Term → Term
invVar m = atVar λ where
    n k [] → if (Dec→Bool (discreteℕ m k) )
              then just (def (quote ~_) v[ var (k + n) [] ])
              else nothing
    _ _ _ → nothing






hasVar : ℕ → Term → Bool
hasVar k' tm = snd $ runIdentity $ (unwrap (atVarM f tm) false)
  where
    f : ℕ → ℕ → List (Arg Term) → Maybe ([ State₀T Bool RMT IdentityF ] Term)
    f n k args = just (wrap (pure ∘S ((var (n + k) args ,_)) ∘S (λ where
        true → true
        false → k =ℕ k'
      )))

hasVarBy : (ℕ → Bool) → Term → Bool
hasVarBy g tm = snd $ runIdentity $ (unwrap (atVarM f tm) false)
  where
    f : ℕ → ℕ → List (Arg Term) → Maybe ([ State₀T Bool RMT IdentityF ] Term)
    f n k args = just (wrap (pure ∘S ((var (n + k) args ,_)) ∘S (λ where
        true → true
        false → g k
      )))



findInterval : ℕ → Term → Maybe Term
findInterval dim tm =
  snd $ runIdentity $ (unwrap {T = State₀T (Maybe Term)} (atVarOrDefM.rv
     (λ n k _ args' →
      let z =  (runIdentity (unwrap args' nothing))
      in wrap (identity ∘S (var k (fst z) ,_) ∘S
             (_mb>> snd z ∘S  _mb>> f n k (fst z))))
     (λ n nm _ args' →
      let z =  (runIdentity (unwrap args' nothing))
      in wrap
           (identity ∘S (def nm (fst z) ,_) ∘S
              (_mb>> snd z
                ∘S _mb>> (map-Maybe (dropVars.rv n zero) (g nm (fst z) (def nm (fst z)))))))
     0 tm) nothing)
  where

    _mb>>_ : Maybe Term → Maybe Term → Maybe Term
    nothing mb>> x₁ = x₁
    just x mb>> _ = just x


    f : ℕ → ℕ → List (Arg Term) → Maybe Term
    f n x [] =
         if (n <ℕ (suc x)) and (x <ℕ (n + dim))
         then just (var (x ∸ n) [])
         else nothing
    f n k (x ∷ args) = nothing

    g :  Name → List (Arg Term) → Term → Maybe Term
    g (quote _∨_) a@(_ v∷ v[ _ ]) tm = just tm
    g (quote _∧_) a@(_ v∷ v[ _ ]) tm = just tm
    g (quote ~_) a@(v[ _ ]) tm = just tm
    g _ _ _ = nothing


replaceVarWithTerm : (ℕ → Maybe Term) → Term → Term
replaceVarWithTerm f =
   atVar λ n k _ →
       map-Maybe (liftVarsFrom n zero) (f k)


substTms : List Term → Term →  Term
substTms xs = dropVars.rv (length xs) zero ∘S replaceVarWithTerm (lookup (map (liftVarsFrom (length xs) 0) xs))

replaceAtTrm : ℕ → Term → Term → Term
replaceAtTrm k t =
 dropVar k ∘ replaceVarWithTerm (z k)

 where
 z : ℕ → ℕ → Maybe Term
 z zero zero = just t
 z zero (suc y) = nothing
 z (suc x) zero = nothing
 z (suc x) (suc y) = z x y


fromJust : ∀ {ℓ} {A : Type ℓ} → List ErrorPart → Maybe A → TC A
fromJust e = Mb.rec (typeError e) pure

liftedTele : Telescope → Telescope
liftedTele [] = []
liftedTele (x ∷ xs) = L.map (map-snd (mapArg liftVars)) (x ∷ liftedTele xs)

macro
 q[_] : Term → Term → TC Unit
 q[_] tm h =
   quoteTC tm >>= quoteTC >=> unify h
