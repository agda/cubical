{-# OPTIONS --safe #-}
module Cubical.Algebra.CommMonoid.CommMonoidProd where

open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.CommMonoid.Base


open CommMonoidStr
open IsCommMonoid hiding (rid ; lid)
open IsMonoid hiding (rid ; lid)
open IsSemigroup


private
  variable
    ℓ ℓ' : Level


CommMonoidProd : CommMonoid ℓ → CommMonoid ℓ' → CommMonoid (ℓ-max ℓ ℓ')
CommMonoidProd M N = makeCommMonoid ε× _·×_ is-set× assoc× rid× comm×
  where
  ε× = (ε (snd M)) , (ε (snd N))
  
  _·×_ = λ x y → _·_ (snd M) (fst x) (fst y) , _·_ (snd N) (snd x) (snd y)
  
  is-set× = isSet× (is-set (snd M)) (is-set (snd N))
  
  assoc× = λ x y z i →  assoc (snd M) (fst x) (fst y) (fst z) i , assoc (snd N) (snd x) (snd y) (snd z) i
  
  rid× = λ x i → rid (snd M) (fst x) i , rid (snd N) (snd x) i
 
  comm× = λ x y i → comm (snd M) (fst x) (fst y) i , comm (snd N) (snd x) (snd y) i
