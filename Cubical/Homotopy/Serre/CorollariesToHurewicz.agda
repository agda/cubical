{-# OPTIONS --lossy-unification --safe #-}
module Cubical.Homotopy.Serre.CorollariesToHurewicz where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Properties
open import Cubical.Homotopy.Loopspace

open import Cubical.CW.Base
open import Cubical.CW.Connected

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.FinitePresentation
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.GroupPath

open import Cubical.HITs.Susp
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as TR

open import Cubical.Homotopy.Serre.FiniteCW
open import Cubical.Homotopy.Serre.FPAbGroup
open import Cubical.Homotopy.Serre.HomotopyGroups
open import Cubical.Homotopy.Serre.SAF
open import Cubical.Homotopy.Serre.LastMinuteLemmas.ConnectedLemmas
open import Cubical.Homotopy.Serre.LastMinuteLemmas.SuspLemmas
open import Cubical.Homotopy.Serre.ConnectedCovers.GeneralisingFreudenthal

private
  variable
    ℓ : Level

  -- Bottom homotopy groups, e.g.,
  -- if n = 0 we are talking about π₂(X),
  -- and X must be simply connected = 1-connected.
  --*** STOCKHOLM ***
isFinCW→isFPBottomπ : (X : Pointed ℓ) (hX : isFinCW (typ X))
  (n : ℕ) (cX : isConnected (3 + n) (typ X))
  → isFP (πAb n X)
isFinCW→isFPBottomπ X hX n cX =
  subst isFP (AbGroupPath _ _ .fst
    (GroupIso→GroupEquiv (π'Gr≅πGr (suc n) X)))
      (isFinitelyPresented-π'connectedCW X (finCW→CW (_ , hX) .snd) n cX)

saf→isFPBottomπ : (X : Pointed ℓ) (hX : saf X)
  (n : ℕ) (cX : isConnected (3 + n) (typ X))
  → isFP (πAb n X)
saf→isFPBottomπ {ℓ = ℓ} X hX n cX =
  PT.rec squash₁ (uncurry λ m →
    PT.rec squash₁
      λ {(CX , f , cf)
      → TR.rec (subst (λ k → isOfHLevel k (isFP (πAb n X)))
                         (+-comm (4 + n) m)
                         (isProp→isOfHLevelSuc (3 + (n + m))
                         squash₁))
                (λ {(x , fp) → main m CX x f fp cf})
                (cf (Susp∙^ m X .snd) .fst)})
    (hX (4 + n))
  where
  ϕ' : ∀ {ℓ} (m : ℕ) (CX : FinCW ℓ) (x : fst CX)
     (f : fst CX → Susp^ m (typ X)) (fp : f x ≡ Susp∙^ m X .snd)
     → GroupEquiv (πGr (1 + (m + n)) (Susp∙^ m X)) (πGr (suc n) X)
  ϕ' zero CX x f fp = idGroupEquiv
  ϕ' (suc m) CX x f fp =
    invGroupEquiv
      (compGroupEquiv
        (connectedFun→πEquiv _ (toSuspPointedω X m) connω) ψ)
    where
    ψ : GroupEquiv (πGr (suc n) ((Ω^ (suc m)) (Susp∙^ (suc m) X)))
                   (πGr (1 + (suc m + n)) (Susp∙^ (suc m) X))

    ψ = compGroupEquiv (GroupIso→GroupEquiv (GrIso-πΩ^-π (suc n) (suc m)))
                       (invEq (GroupPath _ _)
                         (cong₂ πGr (λ i → suc (+-suc m n i)) refl))

    connω : isConnectedFun (4 + n) (fst (toSuspPointedω X m))
    connω b = isConnectedSubtr (4 + n) n
      (subst (λ k → isConnectedFun k (fst (toSuspPointedω X m)))
                  (sym (+-suc n (suc (suc (suc n)))
                  ∙ +-suc (suc n) (suc (suc n))))
                  (toSuspPointedωConnected' {A = X} m (suc n) cX) b)


  module _ (m : ℕ) (CX : FinCW ℓ) (x : fst CX)
    (f : fst CX → Susp^ m (typ X)) (fp : f x ≡ Susp∙^ m X .snd)
    (cf : isConnectedFun (m + suc (suc (suc (suc n)))) f)
    where
    cf' : isConnectedFun (suc (suc (suc (suc (m + n))))) f
    cf' = transport (λ i → isConnectedFun ((+-comm m (4 + n)
                           ∙ (λ i → suc (suc (suc (suc (+-comm n m i)))))) i) f)
                    cf

    ϕ : AbGroupEquiv (πAb (m + n) (Susp∙^ m X)) (πAb n X)
    ϕ = ϕ' m CX x f fp

    ξ : AbGroupEquiv (πAb (m + n) (fst CX , x))
                     (πAb (m + n) (Susp∙^ m X))
    ξ = connectedFun→πEquiv (suc (m + n)) (f , fp) cf'

    connSuspX : isConnected (suc (suc (suc (m + n)))) (Susp^ m (typ X))
    connSuspX = subst (λ k → isConnected k (Susp^ m (typ X)))
      (+-assoc m 3 n ∙ cong (_+ n) (+-comm m 3))
      (isConnectedSusp^ (3 + n) m cX)

    connCX : isConnected (suc (suc (suc (m + n)))) (fst CX)
    connCX = isConnectedCodomain (3 + (m + n)) 1 f connSuspX cf'

    main' : isFP (πAb (m + n) (fst CX , x))
    main' = isFinCW→isFPBottomπ (fst CX , x) (snd CX) (m + n) connCX

    main : isFP (πAb n X)
    main = subst isFP (AbGroupPath _ _ .fst (compGroupEquiv ξ ϕ))
                 main'
