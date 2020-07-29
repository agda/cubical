
{-# OPTIONS --cubical --safe #-}

module Cubical.Data.Group.Action.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Group.Base
open import Cubical.Data.Group.Action.Base
open import Cubical.Data.Sigma
open import Cubical.Foundations.Transport


lActionTransport : {ℓ ℓ' : Level} {G G' : Group ℓ} {X X' : Group ℓ'}
  (α : lAction G X) (α' : lAction G' X')
  (p-G : G ≡ G')
  (p-X : X ≡ X')
  (trAct : (g : Group.type G) (x : Group.type X) →
    transport (λ i → Group.type (p-X i)) (lAction.act α g x)
      ≡ lAction.act α' (transport (λ i → (Group.type (p-G i))) g) (transport (λ i → (Group.type (p-X i))) x))
  → transport (λ i → lAction (p-G i) (p-X i)) α ≡ α'
lActionTransport {ℓ} {ℓ'} {G} {G'} {X} {X'}
  α α' p-G p-X trAct
  = λ i → laction (p-act i) (p-identity i) (p-coh i) (p-hom i)
    where
      p-act = λ (i : I) → {!!}
      p-identity = {!!}
      p-coh = {!!}
      p-hom = {!!}
