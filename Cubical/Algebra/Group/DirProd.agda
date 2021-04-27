{-# OPTIONS --cubical --no-import-sorts --safe #-}
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

dirProd : ∀ {ℓ ℓ'} → Group {ℓ} → Group {ℓ'} → Group
fst (dirProd G H) = fst G × fst H
0g (snd (dirProd G H)) = (0g (snd G)) , (0g (snd H))
_+_ (snd (dirProd G H)) x y = _+_ (snd G) (fst x) (fst y)
                            , _+_ (snd H) (snd x) (snd y)
(inv (snd (dirProd G H))) x = (inv (snd G) (fst x)) , (inv (snd H) (snd x))
is-set (isSemigroup (isMonoid (isGroup (snd (dirProd G H))))) =
  isSet× (is-set (snd G)) (is-set (snd H))
assoc (isSemigroup (isMonoid (isGroup (snd (dirProd G H))))) x y z i =
  assoc (snd G) (fst x) (fst y) (fst z) i , assoc (snd H) (snd x) (snd y) (snd z) i
fst (identity (isMonoid (isGroup (snd (dirProd G H)))) x) i =
  rid (snd G) (fst x) i , rid (snd H) (snd x) i
snd (identity (isMonoid (isGroup (snd (dirProd G H)))) x) i =
  lid (snd G) (fst x) i , lid (snd H) (snd x) i
fst (inverse (isGroup (snd (dirProd G H))) x) i =
  (invr (snd G) (fst x) i) , invr (snd H) (snd x) i
snd (inverse (isGroup (snd (dirProd G H))) x) i =
  (invl (snd G) (fst x) i) , invl (snd H) (snd x) i
