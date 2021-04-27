{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.DirProd
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ₁ ℓ₂ : Level

-- The following definition of GroupHom and GroupEquiv are level-wise heterogeneous.
-- This allows for example to deduce that G ≡ F from a chain of isomorphisms
-- G ≃ H ≃ F, even if H does not lie in the same level as G and F.

isGroupHom : (G : Group {ℓ}) (H : Group {ℓ'}) (f : ⟨ G ⟩ → ⟨ H ⟩) → Type _
isGroupHom G H f = (x y : ⟨ G ⟩) → f (x G.+ y) ≡ (f x H.+ f y) where
  module G = GroupStr (snd G)
  module H = GroupStr (snd H)

record GroupHom (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor grouphom

  field
    fun : ⟨ G ⟩ → ⟨ H ⟩
    isHom : isGroupHom G H fun

record GroupEquiv (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor groupequiv

  field
    eq : ⟨ G ⟩ ≃ ⟨ H ⟩
    isHom : isGroupHom G H (equivFun eq)

  hom : GroupHom G H
  hom = grouphom (equivFun eq) isHom

open GroupHom
open GroupStr

×hom : {A : Group {ℓ}} {B : Group {ℓ'}} {C : Group {ℓ''}} {D : Group {ℓ'''}}
    → GroupHom A C → GroupHom B D → GroupHom (dirProd A B) (dirProd C D)
fun (×hom mf1 mf2) = map-× (fun mf1) (fun mf2)
isHom (×hom mf1 mf2) a b = ≡-× (isHom mf1 _ _) (isHom mf2 _ _)

-- TODO: make G and H implicit?
isInIm : (G : Group {ℓ}) (H : Group {ℓ'}) → GroupHom G H → ⟨ H ⟩ → Type (ℓ-max ℓ ℓ')
isInIm G H ϕ h = ∃[ g ∈ ⟨ G ⟩ ] ϕ .fun g ≡ h

-- TODO: make G and H implicit?
isInKer : (G : Group {ℓ}) (H : Group {ℓ'}) → GroupHom G H → ⟨ G ⟩ → Type ℓ'
isInKer G H ϕ g = ϕ .fun g ≡ 0g (snd H)

Ker : {G : Group {ℓ}} {H : Group {ℓ'}} → GroupHom G H → Type _
Ker {G = G} {H = H} ϕ = Σ[ x ∈ ⟨ G ⟩ ] isInKer G H ϕ x

Im : {G : Group {ℓ}} {H : Group {ℓ'}} → GroupHom G H → Type _
Im {G = G} {H = H} ϕ = Σ[ x ∈ ⟨ H ⟩ ] isInIm G H ϕ x

-- TODO: make G and H implicit?
isSurjective : (G : Group {ℓ}) (H : Group {ℓ'}) → GroupHom G H → Type (ℓ-max ℓ ℓ')
isSurjective G H ϕ = (x : ⟨ H ⟩) → isInIm G H ϕ x

-- TODO: make G and H implicit?
isInjective : (G : Group {ℓ}) (H : Group {ℓ'}) → GroupHom G H → Type (ℓ-max ℓ ℓ')
isInjective G H ϕ = (x : ⟨ G ⟩) → isInKer G H ϕ x → x ≡ 0g (snd G)



-- ----------- Alternative notions of isomorphisms --------------
record GroupIso {ℓ ℓ'} (G : Group {ℓ}) (H : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where

  constructor iso
  field
    map : GroupHom G H
    inv : ⟨ H ⟩ → ⟨ G ⟩
    rightInv : section (GroupHom.fun map) inv
    leftInv : retract (GroupHom.fun map) inv

record BijectionIso {ℓ ℓ'} (A : Group {ℓ}) (B : Group {ℓ'}) : Type (ℓ-max ℓ ℓ') where

  constructor bij-iso
  field
    map' : GroupHom A B
    inj : isInjective A B map'
    surj : isSurjective A B map'

-- "Very" short exact sequences
-- i.e. an exact sequence A → B → C → D where A and D are trivial
record vSES {ℓ ℓ' ℓ'' ℓ'''} (A : Group {ℓ}) (B : Group {ℓ'}) (leftGr : Group {ℓ''}) (rightGr : Group {ℓ'''})
           : Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ'' ℓ''')))) where

  constructor ses
  field
    isTrivialLeft : isProp ⟨ leftGr ⟩
    isTrivialRight : isProp ⟨ rightGr ⟩

    left : GroupHom leftGr A
    right : GroupHom B rightGr
    ϕ : GroupHom A B

    Ker-ϕ⊂Im-left : (x : ⟨ A ⟩)
                  → isInKer A B ϕ x
                  → isInIm leftGr A left x
    Ker-right⊂Im-ϕ : (x : ⟨ B ⟩)
                   → isInKer B rightGr right x
                   → isInIm A B ϕ x
