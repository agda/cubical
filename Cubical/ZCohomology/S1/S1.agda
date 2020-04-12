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

----  H⁰(S¹) = ℤ  ----

coHom0-S1 : coHom zero S¹ ≡ Int
coHom0-S1 = (λ i → ∥ helpLemma i ∥₀ ) ∙ setTruncIdempotent isSetInt
  where
  helpLemma : (S¹ → Int) ≡ Int
  helpLemma = isoToPath (iso fun funinv (λ _ → refl) (λ f → funExt (rinvLemma f)))
    where
    fun : (S¹ → Int) → Int
    fun f = f base

    funinv : Int → (S¹ → Int)
    funinv a base = a
    funinv a (loop i) = a

    rinvLemma : (f : S¹ → Int) → (x : S¹) → funinv (fun f) x ≡ f x
    rinvLemma f  base = refl
    rinvLemma f  (loop i) j = isSetInt (f base) (f base) (λ k → f (loop k)) refl (~ j) i

-------------------------

{- TODO : give Hᵏ(S¹) for all k -}
