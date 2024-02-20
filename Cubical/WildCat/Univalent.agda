{-# OPTIONS --safe #-}
module Cubical.WildCat.Univalent where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma renaming (_×_ to _×'_)

open import Cubical.WildCat.Base

private
  variable
    ℓ ℓ' : Level

open WildCat

-- Equivalences in wild categories (analogous to HoTT-terminology for maps between types)
record isWildCatEquiv (C : WildCat ℓ ℓ') (x y : C .ob) (f : C [ x , y ]) : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  constructor isequiv
  field
    invL : C [ y , x ]
    invR : C [ y , x ]
    isInvL : invL ⋆⟨ C ⟩ f ≡ C .id
    isInvR : f ⋆⟨ C ⟩ invR ≡ C .id

isPropEquiv :
  (C : WildCat ℓ ℓ') (x y : ob C) (f : C [ x , y ])
  → isProp (isWildCatEquiv C x y f)
isPropEquiv C x y f isEquiv1 isEquiv2 = {!!}
  where
    {- Use that equivalences have unique right/left inverses -}
    open isWildCatEquiv
    lInv1 = isEquiv1 .invL
    lInvUnique : (g : C [ y , x ]) → g ⋆⟨ C ⟩ f ≡ C .id → g ≡ lInv1
    lInvUnique = {!!}

WildCatEquiv : (C : WildCat ℓ ℓ') (x y : ob C) → Type _
WildCatEquiv C x y = Σ[ f ∈ C [ x , y ] ] isWildCatEquiv C x y f

idWildEquiv : {C : WildCat ℓ ℓ'} {x : C .ob} → WildCatEquiv C x x
idWildEquiv {C = C} = (C .id ) , isequiv (C .id ) (C .id ) (C .⋆IdL (C .id)) (C .⋆IdL (C .id))

pathToEquiv : {C : WildCat ℓ ℓ'} {x y : C .ob} (p : x ≡ y) → WildCatEquiv C x y
pathToEquiv {C = C} p = J (λ z _ → WildCatEquiv C _ z) idWildEquiv p

-- Univalent Categories
record isUnivalent (C : WildCat ℓ ℓ') : Type (ℓ-max ℓ ℓ') where
  no-eta-equality
  field
    univ : (x y : C .ob) → isEquiv (pathToEquiv {C = C} {x = x} {y = y})
