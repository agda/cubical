{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.Automorphism where

open import Cubical.Core.Everything
open import Cubical.Data.Group.Base
open import Cubical.Data.Group.Higher
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Prelude hiding (comp)


-- AutomorphismGroup : {ℓ : Level} {A : Type ℓ} (a : A) → HigherGroup ℓ
-- AutomorphismGroup a = highergroup ((a ≡ a) , refl) {!!}

Aut : {ℓ : Level} (G : Group ℓ) → Group ℓ
Aut (group type setStruc (group-struct id inv comp lUnit rUnit assoc lCancel rCancel)) = group {!!} {!!} {!!}
