{-# OPTIONS --safe #-}
module Cubical.Algebra.Group.DirProd where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup

open GroupStr
open IsGroup hiding (rid ; lid ; invr ; invl)
open IsMonoid hiding (rid ; lid)
open IsSemigroup

DirProd : ∀ {ℓ ℓ'} → Group ℓ → Group ℓ' → Group (ℓ-max ℓ ℓ')
fst (DirProd G H) = fst G × fst H
1g (snd (DirProd G H)) = (1g (snd G)) , (1g (snd H))
_·_ (snd (DirProd G H)) x y = _·_ (snd G) (fst x) (fst y)
                            , _·_ (snd H) (snd x) (snd y)
(inv (snd (DirProd G H))) x = (inv (snd G) (fst x)) , (inv (snd H) (snd x))
is-set (isSemigroup (isMonoid (isGroup (snd (DirProd G H))))) =
  isSet× (is-set (snd G)) (is-set (snd H))
assoc (isSemigroup (isMonoid (isGroup (snd (DirProd G H))))) x y z i =
  assoc (snd G) (fst x) (fst y) (fst z) i , assoc (snd H) (snd x) (snd y) (snd z) i
fst (identity (isMonoid (isGroup (snd (DirProd G H)))) x) i =
  rid (snd G) (fst x) i , rid (snd H) (snd x) i
snd (identity (isMonoid (isGroup (snd (DirProd G H)))) x) i =
  lid (snd G) (fst x) i , lid (snd H) (snd x) i
fst (inverse (isGroup (snd (DirProd G H))) x) i =
  (invr (snd G) (fst x) i) , invr (snd H) (snd x) i
snd (inverse (isGroup (snd (DirProd G H))) x) i =
  (invl (snd G) (fst x) i) , invl (snd H) (snd x) i
