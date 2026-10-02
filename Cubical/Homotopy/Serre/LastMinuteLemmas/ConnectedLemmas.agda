{-# OPTIONS --safe #-}
module Cubical.Homotopy.Serre.LastMinuteLemmas.ConnectedLemmas where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎

open import Cubical.CW.Base
open import Cubical.CW.Instances.Empty
open import Cubical.CW.Instances.Sigma

open import Cubical.HITs.Pushout
open import Cubical.HITs.SmashProduct
open import Cubical.HITs.SmashProduct.SymmetricMonoidal
open import Cubical.HITs.Wedge
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Susp

open import Cubical.Homotopy.Connected

open import Cubical.Homotopy.Serre.FiniteCW
open import Cubical.Homotopy.Serre.LastMinuteLemmas.SuspLemmas

private
  variable
    ℓ : Level

-- move to Cubical.Homotopy.Connected
Susp^-conn : (m n : ℕ) (X : Type ℓ) → isConnected m X
             → isConnected (n + m) (Susp^ n X)
Susp^-conn m zero X hX = hX
Susp^-conn m (suc n) X hX =
  transport (λ i → isConnected (+-suc n m i) (Susp^ (suc n) X))
             (Susp^-conn (suc m) n (Susp X) (isConnectedSusp m hX))

-- move to Cubical.Homotopy.Connected
isConnectedFunCompMin : ∀ {ℓA ℓB ℓC}
  {A : Type ℓA} {B : Type ℓB} {C : Type ℓC}
  (n m : ℕ) (f : A → B) (g : B → C)
  → isConnectedFun n f → isConnectedFun m g
  → isConnectedFun (min n m) (g ∘ f)
isConnectedFunCompMin n m f g cf cg =
  isConnectedComp g f (min n m)
    (isConnectedFunSubtr (min n m)
      (fst (min-≤-left {m = m} {n})) _
    (subst (λ k → isConnectedFun k g)
      (sym (snd (min-≤-left {m = m} {n}))
      ∙ cong (fst (min-≤-left {m = m} {n}) +_)
            (minComm m n)) cg))
    (isConnectedFunSubtr (min n m)
      (fst (min-≤-left {m = n} {m})) _
    (subst (λ k → isConnectedFun k f)
      (sym (snd (min-≤-left {m = n} {m}))) cf))

-- move to Cubical.Homotopy.Connected
isConnectedCodomain : ∀ {ℓ} {A B : Type ℓ}
  (n m : ℕ) (f : A → B)
  → isConnected n B
  → isConnectedFun (m + n) f
  → isConnected n A
isConnectedCodomain n m f cA cf =
  isOfHLevelRespectEquiv zero
    (invEquiv (connectedTruncEquiv n f
      (λ b → isConnectedSubtr n m (cf b))))
      cA

-- move to Cubical.Homotopy.Connected
isConnectedSusp^ : {X : Type ℓ} (n m : HLevel)
  → isConnected n X → isConnected (m + n) (Susp^ m X)
isConnectedSusp^ n zero cX = cX
isConnectedSusp^ {X = X} n (suc m) cX =
  subst (isConnected (suc (m + n))) (sym (Susp^-comm m X))
    (isConnectedSusp (m + n) (isConnectedSusp^ n m cX))

-- move to Cubical.Homotopy.Connected
isConnectedSusp^Fun : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B)
  (n m : ℕ) → isConnectedFun n f → isConnectedFun (m + n) (Susp^Fun f m)
isConnectedSusp^Fun f n zero cf = cf
isConnectedSusp^Fun f n (suc m) cf =
  subst (λ k → isConnectedFun k (Susp^Fun (suspFun f) m))
         (+-suc m n)
         (isConnectedSusp^Fun (suspFun f) (suc n) m
           (isConnectedSuspFun _ n cf))

-- move to Cubical.Data.Nat.Properties
min-diag : (a : ℕ) → min a a ≡ a
min-diag zero = refl
min-diag (suc a) = minSuc ∙ cong suc (min-diag a)
