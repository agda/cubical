{-# OPTIONS --safe #-}
module Cubical.Algebra.CommMonoid.CommMonoidProd where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommMonoid.Base


open CommMonoidStr
open IsCommMonoid hiding (rid ; lid)
open IsMonoid hiding (rid ; lid)
open IsSemigroup


CommMonoidProd : ∀ {ℓ ℓ'} → CommMonoid ℓ → CommMonoid ℓ' → CommMonoid (ℓ-max ℓ ℓ')

fst (CommMonoidProd M N) = fst M × fst N

ε (snd (CommMonoidProd M N)) = (ε (snd M)) , (ε (snd N))

_·_ (snd (CommMonoidProd M N)) x y = _·_ (snd M) (fst x) (fst y)
                            , _·_ (snd N) (snd x) (snd y)

is-set (isSemigroup (isMonoid (isCommMonoid (snd (CommMonoidProd M N))))) =
  isSet× (is-set (snd M)) (is-set (snd N))

assoc (isSemigroup (isMonoid (isCommMonoid (snd (CommMonoidProd M N))))) x y z i =
  assoc (snd M) (fst x) (fst y) (fst z) i , assoc (snd N) (snd x) (snd y) (snd z) i

fst (identity (isMonoid (isCommMonoid (snd (CommMonoidProd M N)))) x) i =
  rid (snd M) (fst x) i , rid (snd N) (snd x) i
  
snd (identity (isMonoid (isCommMonoid (snd (CommMonoidProd M N)))) x) i =
  lid (snd M) (fst x) i , lid (snd N) (snd x) i

comm (isCommMonoid (snd (CommMonoidProd M N))) x y i =
  comm (snd M) (fst x) (fst y) i , comm (snd N) (snd x) (snd y) i
