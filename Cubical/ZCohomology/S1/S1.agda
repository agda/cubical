{-# OPTIONS --cubical --safe #-}
module Cubical.ZCohomology.S1.S1 where

open import Cubical.ZCohomology.Base
open import Cubical.ZCohomology.Properties
open import Cubical.HITs.S1
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.SetTruncation
open import Cubical.HITs.Nullification
open import Cubical.Data.Int
open import Cubical.Data.Nat
open import Cubical.HITs.Truncation

private
  variable
    ℓ : Level
    A : Type ℓ


----  H⁰(S¹) ----

coHom0-S1 : (coHom zero S¹) ≡ Int
coHom0-S1 = (λ i → ∥ helpLemma i ∥₀ )  ∙  (setId isSetInt)
  where
  helpLemma : (S¹ → Int) ≡ Int
  helpLemma = isoToPath (iso fun
                             funinv
                             (λ b → refl)
                             λ f → funExt (λ x → rinvLemma f x))
    where
    fun : (S¹ → Int) → Int
    fun f = f base

    funinv : Int → (S¹ → Int)
    funinv a base = a
    funinv a (loop i) = refl {x = a} i

    rinvLemma : ( f : (S¹ → Int)) →
                (x : S¹) →
                funinv (fun f) x ≡ f x
    rinvLemma f  base = refl
    rinvLemma f  (loop i) = sym (helper f i)   where
      helper : (f : (S¹ → Int))  →
               (i : I) →
               (f (loop i) ≡ f base)
      helper f i =  (λ l → ((isSetInt (f base) (f base) (λ k → (f (loop k))) refl) l) i)

-------------------------

{- TODO : give Hᵏ(S¹) for all k -}
