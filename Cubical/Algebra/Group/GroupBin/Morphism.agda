{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Algebra.Group.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.Group.Base
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level

-- The following definition of GroupHom and GroupEquiv are level-wise heterogeneous.
-- This allows for example to deduce that G ≡ F from a chain of isomorphisms
-- G ≃ H ≃ F, even if H does not lie in the same level as G and F.

isGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) (f : ⟨ G ⟩ → ⟨ H ⟩) → Type _
isGroupHom G H f = (x y : ⟨ G ⟩) → f (x G.+ y) ≡ (f x H.+ f y) where
  module G = Group G
  module H = Group H

record GroupHom (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor grouphom
  no-eta-equality
  field
    fun : ⟨ G ⟩ → ⟨ H ⟩
    isHom : isGroupHom G H fun

record GroupEquiv (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor groupequiv
  no-eta-equality
  field
    eq : ⟨ G ⟩ ≃ ⟨ H ⟩
    isHom : isGroupHom G H (equivFun eq)

  hom : GroupHom G H
  hom = grouphom (equivFun eq) isHom

open GroupHom
open GroupEquiv

η-hom : {G : Group {ℓ}} {H : Group {ℓ'}} → (a  : GroupHom G H)
      → grouphom (fun a) (isHom a) ≡ a
fun (η-hom a i) = fun a
isHom (η-hom a i) = isHom a

η-equiv : {G : Group {ℓ}} {H : Group {ℓ'}} → (a  : GroupEquiv G H)
       → groupequiv (eq a) (isHom a) ≡ a
eq (η-equiv a i) = eq a
isHom (η-equiv a i) = isHom a

×hom : ∀ {ℓ ℓ' ℓ'' ℓ'''} {A : Group {ℓ}} {B : Group {ℓ'}} {C : Group {ℓ''}} {D : Group {ℓ'''}}
    → GroupHom A C → GroupHom B D → GroupHom (dirProd A B) (dirProd C D)
fun (×hom mf1 mf2) = map-× (fun mf1) (fun mf2)
isHom (×hom mf1 mf2) a b = ≡-× (isHom mf1 _ _) (isHom mf2 _ _)

open Group

isInIm : ∀ {ℓ ℓ'} (G : Group {ℓ}) (H : Group {ℓ'}) → (GroupHom G H)
       → ⟨ H ⟩ → Type (ℓ-max ℓ ℓ')
isInIm G H ϕ h = ∃[ g ∈ ⟨ G ⟩ ] (fun ϕ) g ≡ h

isInKer : ∀ {ℓ ℓ'} (G : Group {ℓ}) (H : Group {ℓ'}) → (GroupHom G H)
       → ⟨ G ⟩ → Type ℓ'
isInKer G H ϕ g = (fun ϕ) g ≡ 0g H

isSurjective : ∀ {ℓ ℓ'} (G : Group {ℓ}) (H : Group {ℓ'}) → GroupHom G H → Type (ℓ-max ℓ ℓ')
isSurjective G H ϕ = (x : ⟨ H ⟩) → isInIm G H ϕ x

isInjective : ∀ {ℓ ℓ'} (G : Group {ℓ}) (H : Group {ℓ'}) → GroupHom G H → Type (ℓ-max ℓ ℓ')
isInjective G H ϕ = (x : ⟨ G ⟩) → isInKer G H ϕ x → x ≡ 0g G
